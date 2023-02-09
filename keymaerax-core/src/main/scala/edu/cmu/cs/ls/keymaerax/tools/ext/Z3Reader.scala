/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.btactics.{Ax, EqualityTactics, Idioms, SequentCalculus, TactixLibrary, UnifyUSCalculus}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{QE, eqL2R, prop, propClose}
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, InterpretedSymbols}
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig}
import smtlib.theories.Reals
import smtlib.trees.Terms
import smtlib.trees.Terms.{Exists, Forall, Term, _}

import java.io.{Reader, StringReader}
import scala.collection.immutable.IndexedSeq
import scala.collection.mutable

/** Reads [[Expression]]s from SMT-LIB format: converts every (assert X) statement into an expression. */
object Z3Reader {

  type CTerm = edu.cmu.cs.ls.keymaerax.core.Term

  def read(r: Reader): Provable = {
    /** The SMT-Lib lexer is used for token extraction */
    val lexer = new smtlib.lexer.Lexer(r)
    val parser = new smtlib.parser.Parser(lexer)
    val sExpr = parser.parseSExpr

    val terms = scala.collection.mutable.Map.empty[String, CTerm]
    val fmls = scala.collection.mutable.Map.empty[String, Formula]
    val proofs = scala.collection.mutable.Map.empty[String, Provable]

    convertProofTerm(sExpr, terms, fmls, proofs)
  }

  private def convertTerm(t: Terms.SExpr, terms: mutable.Map[String,CTerm],
                          fmls: mutable.Map[String, Formula],
                          proofs: mutable.Map[String, Provable]): CTerm = t match {
    // numbers
    case Reals.NumeralLit(n) =>
      Number(BigDecimal(n))
    case Reals.DecimalLit(n) =>
      Number(n)

    // numeric operators
    case SList(List(SSymbol("-"), f)) => Neg(convertTerm(f, terms, fmls, proofs))
    case SList(SSymbol("+") :: fs) => applyBinaryOperator(fs, Plus, terms, fmls, proofs)
    case SList(SSymbol("-") :: fs) => applyBinaryOperator(fs, Minus, terms, fmls, proofs)
    case SList(SSymbol("*") :: fs) => applyBinaryOperator(fs, Times, terms, fmls, proofs)
    case SList(SSymbol("/") :: fs) => applyBinaryOperator(fs, Divide, terms, fmls, proofs)

    // case if x is a term variable
    case SSymbol(f) =>
      val x = 'R' + f.substring(1)
      if (f(0) == '?' && terms.contains(x))
        terms(x)
      else Variable(f)

    case _ =>
      throw new IllegalArgumentException("Symbol parsed does not match any terms")
  }

  // binary operators can take in any number of args
  private def applyBinaryOperator(ts: List[Terms.SExpr], f: (CTerm, CTerm) => CTerm,
                            terms: mutable.Map[String,CTerm],
                            fmls: mutable.Map[String, Formula],
                            proofs: mutable.Map[String, Provable]): CTerm = ts match {
    case t :: Nil => convertTerm(t, terms, fmls, proofs)
    case t :: rest => f(convertTerm(t, terms, fmls, proofs), applyBinaryOperator(rest, f, terms, fmls, proofs))
    case _ => throw new IllegalArgumentException("Found binary operator with 1 or less arguments")
  }

  private def convertFormula(t: Terms.SExpr, terms: mutable.Map[String,CTerm],
                             fmls: mutable.Map[String, Formula],
                             proofs: mutable.Map[String, Provable]): Formula = t match {
    // bool constants
    case SSymbol("false") => False
    case SSymbol("true") => True

    // real comparison operators
    case SList(List(SSymbol("="), f1, f2)) =>
      try {
        // equality case (term inputs)
        Equal(convertTerm(f1, terms, fmls, proofs),
          convertTerm(f2, terms, fmls, proofs))
      } catch {
        // equivalence case (formula inputs)
        case _ => Equiv(convertFormula(f1, terms, fmls, proofs),
          convertFormula(f2, terms, fmls, proofs))
      }
    case SList(List(SSymbol("<"), f1, f2)) =>
      Less(convertTerm(f1, terms, fmls, proofs),
        convertTerm(f2, terms, fmls, proofs))
    case SList(List(SSymbol("<="), f1, f2)) =>
      LessEqual(convertTerm(f1, terms, fmls, proofs),
        convertTerm(f2, terms, fmls, proofs))
    case SList(List(SSymbol(">"), f1, f2)) =>
      Greater(convertTerm(f1, terms, fmls, proofs),
        convertTerm(f2, terms, fmls, proofs))
    case SList(List(SSymbol(">="), f1, f2)) =>
      GreaterEqual(convertTerm(f1, terms, fmls, proofs),
        convertTerm(f2, terms, fmls, proofs))

    // boolean operators
    case SList(List(SSymbol("not"), f)) =>
      Not(convertFormula(f, terms, fmls, proofs))
    case SList(SSymbol("or") :: fs) =>
      val fsConverted = fs.map(convertFormula(_, terms, fmls, proofs))
      fsConverted.reduce(Or)
    case SList(SSymbol("and") :: fs) =>
      val fsConverted = fs.map(convertFormula(_, terms, fmls, proofs))
      fsConverted.reduce(And)
    case SList(SSymbol("=>") :: fs) =>
      val fsConverted = fs.map(convertFormula(_, terms, fmls, proofs))
      fsConverted.reduce(Imply)

    // SList(SSymbol(“x”) +: rest) =>

    // case if x is a formula variable
    case SSymbol(f) =>
      val x = 'B' + f.substring(1)
      if (f(0) == '$' && fmls.contains(x))
        fmls(x)
      else PredOf(Function(f, None, Unit, Bool), Nothing)

    case _ =>
      throw new IllegalArgumentException("Symbol parsed does not match any formulas")
  }

  private def convertProofTerm(t: Terms.SExpr, terms: mutable.Map[String,CTerm],
                               fmls: mutable.Map[String, Formula],
                               proofs: mutable.Map[String, Provable]): Provable = t match {
    // fix for this
    case SList(List(SList(List(SSymbol("proof"), f)))) =>
      convertProofTerm(f, terms, fmls, proofs)
    case SList(List(SSymbol("proof"), f)) =>
      convertProofTerm(f, terms, fmls, proofs)

    case SList(List(SSymbol("let"), SList(List(SList(List(SSymbol(decl), assignment)))), rest)) =>
      // check for variable type
      println("Initializing Z3 variable " + decl)
      var nVar = ""
      decl(0) match {
        case '?' => // real
          nVar = "R" + decl.substring(1)
          terms(nVar) = convertTerm(assignment, terms, fmls, proofs)
          assert(!terms.isEmpty)
        case '$' => // bool
          nVar = "B" + decl.substring(1)
          fmls(nVar) = convertFormula(assignment, terms, fmls, proofs)
        case '@' => // proof
          nVar = "P" + decl.substring(1)
          proofs(nVar) = convertProofTerm(assignment, terms, fmls, proofs)
        case _ => throw new IllegalArgumentException(
          "Z3 variable \"" + decl + "\" doesn't match any valid syntax")
      }
      convertProofTerm(rest, terms, fmls, proofs)

    case SList(List(SSymbol("asserted"), p)) => (
      Provable.startProof(Sequent(IndexedSeq(convertFormula(p, terms, fmls, proofs)),
        IndexedSeq(convertFormula(p, terms, fmls, proofs))))
      (Close(AntePos(0), SuccPos(0)), 0))

    case SList(List(SSymbol("rewrite"), sfml)) =>
      val fml = convertFormula(sfml, terms, fmls, proofs)
      fml match {
        case e: Equiv =>
          TactixLibrary.proveBy(e, propClose | QE).underlyingProvable
//          val eProof = TactixLibrary.proveBy(e, propClose).underlyingProvable
//          Provable.startProof(q)(CutRight(p, SuccPos(0)), 0)(
//            EquivifyRight(SuccPos(0)), 1)(eProof, 1)
        case c: Equal =>
          TactixLibrary.proveBy(c, QE).underlyingProvable
        case f => TactixLibrary.proveBy(f, TactixLibrary.autoClose).underlyingProvable
      }

    // (mp (proof term of P) (proof term of P->Q) Q)
    case SList(List(SSymbol("mp"), p, pq, q1)) =>
      val pProof = convertProofTerm(p, terms, fmls, proofs)
      val pqProof = convertProofTerm(pq, terms, fmls, proofs)
      val assumption = pProof.conclusion.succ.head
      val Equiv(_, q2) = pqProof.conclusion.succ.head
      assert(convertFormula(q1, terms, fmls, proofs) == q2)
      val pStep0 = Provable.startProof(Sequent(pProof.conclusion.ante ++ pqProof.conclusion.ante,
        IndexedSeq(q2)))(CutRight(assumption, SuccPos(0)), 0)(EquivifyRight(SuccPos(0)), 1)
      val pStep1 = Idioms.timesP(HideLeft(AntePos(0)), pProof.conclusion.ante.size)(pStep0.sub(1))
      pStep0(pStep1, 1)(pqProof, 1)(pProof, 0)

    // (trans (f ~ g) (g = h) (f ~ h))
    case SList(List(SSymbol("trans"), r, e, q)) =>
      val rProof = convertProofTerm(r, terms, fmls, proofs)
      val eProof = convertProofTerm(e, terms, fmls, proofs)
      val qFml = convertFormula(q, terms, fmls, proofs)

      eProof.conclusion.succ.head match {
        case Equiv(ep, eq) =>
          val p0 = Provable.startProof(qFml)
          val p0sig = ProvableSig.startPlainProof(False).reapply(p0)
          val Equiv(_, eqCheck) = p0sig.subgoals(0).succ.head
          assert(eq == eqCheck)
          val p1 = p0sig(UnifyUSCalculus.CEat(ProvableSig.startPlainProof(False).reapply(eProof), PosInExpr(List(1)))(
            SuccPosition(1, List(1))), 0)
          p1.underlyingProvable(rProof, 0)
        case e @ Equal(ep, eq) =>
          // case on steps
          // ensure cut result is valid
          val p0 = ProvableSig.startPlainProof(qFml)(Cut(e), 0)
          val p1 = p0(CoHideRight(SuccPos(1)), 1)(ProvableSig.startPlainProof(False).reapply(eProof), 1)
          val p2 = p1(TactixLibrary.exhaustiveEqL2R(hide=true)(AntePos(0)), 0)
          p2.underlyingProvable

      }
      // Provable.startProof(qFml)(Cut(eProof), 0)(Proof(eProof), 1)(eqR2L(-1), 0)
      // UnifyUSCalculus.scala CEat(fact: Provable) line 1315
      // line 1366: key says which side to rewrite
      // key: PosInExpr(List(0)) rewrites left to right
      // PosInExpr(List(1)) rewrites right to left ****
      // position to apply: position of h in qFml
      //   SuccPosition.base0(0, PosInExpr(List(1)))

    // (monotonicity p_equalities f_equality)
    case SList(SSymbol("monotonicity") :: ps) =>
      val fml = convertFormula(ps.last, terms, fmls, proofs)
      val eProofs = ps.dropRight(1).map(convertProofTerm(_, terms, fmls, proofs))
      val conclusion = eProofs(0).conclusion.succ.head

      val applyReflexive: Provable=>Provable = (pr0: Provable) => {
        var pr: Provable = pr0
        for (i <- pr.subgoals.length - 1 to 0 by -1) {
          pr.subgoals(i).succ match {
            case _: Equal =>
              pr = pr(UnifyUSCalculus.byUS(
                Ax.equalReflexive.provable).apply(
                ElidingProvable(pr.sub(i), 0, Declaration(Map.empty))).underlyingProvable,
                pr.subgoals.length - 1)
            case _: Equiv =>
              pr = pr(UnifyUSCalculus.byUS(
                Ax.equivReflexive.provable).apply(
                ElidingProvable(pr.sub(i), 0, Declaration(Map.empty))).underlyingProvable,
                pr.subgoals.length - 1)
          }
        }
        pr
      }

      val fProof = ProvableSig.startPlainProof(Sequent(eProofs(0).conclusion.ante, IndexedSeq(fml)))
      val eProofSig = ProvableSig.startPlainProof(False).reapply(eProofs(0))

      var p1 = ProvableSig.startPlainProof(eProofs(0).conclusion.toFormula)
      p1 = p1(ImplyRight(SuccPos(0)), 0)(eProofSig, 0)

      if (false){
        val proof = Provable.startProof(Sequent(eProofs(0).conclusion.ante,
          IndexedSeq(fml)))(CutRight(conclusion, SuccPos(0)), 0)

        val applyEq: Provable=>Provable = (pr: Provable) => TactixLibrary.proveBy(
          ElidingProvable(pr, 0, Declaration(Map.empty)),
          eqL2R(-1 - eProofs(0).conclusion.ante.size)(1)).underlyingProvable

        val pir = proof(ImplyRight(SuccPos(0)), 1)
        val proof1 = pir(applyEq(pir.sub(1)), 1)
        val p1withE1 = proof1(eProofs(0), 0)
        val p1withE = p1withE1(CoHideRight(SuccPos(0)), p1withE1.subgoals.length - 1)
        p1 = ProvableSig.startPlainProof(False).reapply(p1withE)
      }

      val applyPos = conclusion match {
        case Equal(l, _) =>
          FormulaTools.posOf(fml, l)
        case Equiv(l, _) =>
          FormulaTools.posOf(fml, l)
      }

      applyPos match {
        case Some(pos) =>
          val p2 = fProof(UnifyUSCalculus.useAt(p1, PosInExpr(List(1,0)))(SuccPosition.base0(0, pos.parent)))
          val p3 = applyReflexive(p2.underlyingProvable)
          assert(p3.isProved)
          p3
        case None => throw new IllegalArgumentException(
          "Did not locate the conclusion within the formula")
      }

    // (not-or-elim not-or-chain conclusion)
    // NOTE: copy mp assumptions casing
    case SList(SSymbol(step) :: ps) if step == "not-or-elim" || step == "and-elim" =>
      val fml = convertFormula(ps.last, terms, fmls, proofs)
      val cProofs = ps.dropRight(1).map(convertProofTerm(_, terms, fmls, proofs))

      // does not support multiple proof terms yet
      assert(cProofs.length == 1)
      val conclusion = cProofs(0).conclusion.succ.head

      // output formula includes negation
      val proof = Provable.startProof(Sequent(cProofs(0).conclusion.ante,
        IndexedSeq(fml)))(CutRight(conclusion, SuccPos(0)), 0)
      val apply = TactixLibrary.proveBy(Sequent(cProofs(0).conclusion.ante,
        IndexedSeq(Imply(conclusion, fml))), prop).underlyingProvable
    proof(apply, 1)(cProofs(0), 0)

    // case if x is a proof variable
    case SSymbol(f) =>
      val x = "P" + f.substring(1)
      if (f(0) == '@' && proofs.contains(x))
        proofs(x)
      else throw new IllegalArgumentException(
        "Z3 proof term variable \"" + f + "\" used before declaration")

    case x =>
      print(x)
      throw new IllegalArgumentException("Symbol parsed does not match any proof terms")
  }

}
