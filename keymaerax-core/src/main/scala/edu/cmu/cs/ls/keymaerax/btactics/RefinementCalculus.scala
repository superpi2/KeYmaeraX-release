/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._

/**
  * A sequent calculus for dRL.
  *
  * @author Nathan Fulton
  */
object RefinementCalculus {
  //region Refinement proofs rules

  lazy val boxRefineAxiom = "boxRefineAxiom" by HilbertCalculus.byUS("[=<]")

  /**
    * Note that the [a;]p(??) goal must be top-level and the only subgoal in the succedent. These contraints can and should
    * be relaxed.
    * {{{
    *   \Gamma |- [b;]p(??)   \Gamma |- a =< b
    *   ----------------------------------------------
    *         \Gamma |- [a;]p(??)
    * }}}
    *
    * @todo There should be a more general-purpose way of doing usubsts proofs like this.
    * @todo generalize this to non-top-level positions.
    */
  def boxRefine(b: Program) : DependentPositionWithAppliedInputTactic = "boxRefine" by (b, (provable: Provable, pos: Position) => {
    //@note If any of these asserts fail then the tactic is considered not applicable.
    assert(provable.subgoals.length==1)
    assert(pos.isSucc)
    assert(provable.subgoals(0).succ.length == 1) //@todo probably not necessary even in niave implementation.
    assert(provable.subgoals(0).succ(pos.topLevel.index0).isInstanceOf[Box])

    val Box(a,p)  = provable.subgoals(0).succ(pos.topLevel.index0) //Justified by above asserts.
    val ruleAxiom = Imply(And(Box(b,p), Refinement(a,b)), Box(a,p)) //US instance of boxRefine axiom

    /*
     * The output tactic constructs a proof of the form:
     *                           |- [b]p         |- a =< b
     *                          ------------------------------- andR resulting in 2 open goals (as desired)
     *         *                 |- [b]p & a =< b
     * ----------------------   ------------------------------- US to [=<] axiom on left branch, imply rw on right branch
     * [a]p <- [b]p & a =< b   [a]p <- [b]p & a =< b |- [a]p
     * -------------------------------------------------------- cut in [[equiv]]
     *                      |- [a]p
     *
     * See Slide 10 of http://nfulton.org/slides/cpp16.pdf
     * @todo CE/CEat instead?
     * @note It might be a better idea to *not* split the conjunction so that the subgoal's position is stable wrt [a]p.
     *       This is only relevant, however, if we allow this tactic to be used in context.
     */
    PartialTactic(TactixLibrary.cut(ruleAxiom) <(
      PartialTactic(implicationRewriting('Llast) & TactixLibrary.andR('Rlast)),
      PartialTactic(TactixLibrary.cohide('Rlast) & boxRefineAxiom)
    ))
  })

  //endregion

  //region Idempotent Semiring axioms for proving refinements

//  /** Attempts to automatically prove that a =< b by applying idempotent semiring axioms.
//    *
//    * @todo come up with a good tactic modulo odes(/loops?) based on a KAT DP?
//    */
//  lazy val proveRefinement: DependentPositionTactic = ???

  /**
    * Proves
    * {{{
    *   a; =< a;
    * }}}
    */
  lazy val refineId : BelleExpr = "refineId" by HilbertCalculus.byUS("refine id")

  /**
    * {{{
    *   a; == a;
    * }}}
    */
  lazy val refineEquivRefl : BelleExpr = "refineEquivRefl" by HilbertCalculus.byUS("refine equiv refl")

  lazy val refineTrivialCloser : BelleExpr = "refineTrivialCloser" by (refineId | refineEquivRefl)

  /**
    * Proves
    * {{{
    *   {a; ++ b;} == {b; ++ a;}
    * }}}
    */
  lazy val refineChoiceComm : BelleExpr = "refineChoiceComm" by HilbertCalculus.byUS("refine choice comm")
  //@todo add a tactic that rewrites {a; ++ b;} to {b; ++ a;} in a context.

  lazy val programEquivComm : BelleExpr = "programEquivComm" by HilbertCalculus.byUS("program equiv comm")

  /**
    * {{{
    *   a; ?true; == a;
    * }}}
    */
  lazy val composeIdR : BelleExpr = "composeIdR" by HilbertCalculus.byUS("compose id right")

  /**
    * {{{
    *   a; == a; ?true;
    * }}}
    */
  lazy val composeIdRi : BelleExpr = "composeIdRi" by programEquivComm & composeIdR

  //endregion

  //region Proof rules from Fig. 4, reformulated as axioms.

  lazy val refineAntisym : BelleExpr = "refineAntisym" by HilbertCalculus.byUS("refine antisym")
  lazy val refineAntisymRule : DependentPositionTactic = "refineAntisymRule" by ((pos:Position, s: Sequent) => {
    import Augmentors._
    //Computes a uniform substitution instance of the axiom for use in implicational rewriting using CEat.
    //Otherwise if we use CEat (with no context) then we wend up trying to prove a uniform subst instance of the axiom
    //using the literal axiom, which obviously won't do.
    //@todo is there a better (or at least standardized) way of doing this?
    //@note contexutal CEat might be intended for this sort of thing but I'm not too familiar with that.
    //@todo if not then move this into a core library; maybe UnifyUSCalculus.
    val axiom = AxiomInfo.ofCodeName("refineAntisym")

    val (a,b) = axiom.formula match {
      case Imply(_, ProgramEquiv(a,b)) => (a,b)
      case _ => throw new Exception(s"Expected axiom of form a==b -> ... but found ${axiom.formula}")
    }

    val (aRepl, bRepl) = s(pos) match {
      case ProgramEquiv(l,r) => (l,r)
      case _ => throw new Exception(s"Expected program equivalence formula but found ${s(pos).prettyString}")
    }

    val axiomInstance = USubst(a ~> aRepl :: b ~> bRepl :: Nil)(axiom.provable)

    (HilbertCalculus.CEat(axiomInstance)(pos) & TactixLibrary.andR(pos)).partial
  })

  lazy val refineUnloop : BelleExpr = "refineUnloop" by HilbertCalculus.byUS("refine unloop")
  lazy val refineUnloopRule : DependentPositionTactic = "refineUnloopRule" by((pos: Position, s: Sequent) => {
    import Augmentors._
    val axiom = AxiomInfo.ofCodeName("refineUnloop")

    val (a,b) = axiom.formula match {
      case Imply(_, Refinement(Loop(a),Loop(b))) => (a,b)
      case _ => throw new Exception(s"Expected axiom of form a*=<b* -> ... but found ${axiom.formula}")
    }

    val (aRepl, bRepl) = s(pos) match {
      case Refinement(Loop(l),Loop(r)) => (l,r)
      case _ => throw new Exception(s"Expected program refinement formula but found ${s(pos).prettyString}")
    }

    val axiomInstance = USubst(a ~> aRepl :: b ~> bRepl :: Nil)(axiom.provable)

    HilbertCalculus.CEat(axiomInstance)(pos)
  })

  lazy val refineCompose : BelleExpr = "refineCompose" by HilbertCalculus.byUS("refine (;)")
  lazy val refineComposeRule : DependentPositionTactic = "refineComposeRule" by((pos: Position, s: Sequent) => {
    import Augmentors._
    val axiom = AxiomInfo.ofCodeName("refineCompose")

    val (a1,b1, a2, b2) = axiom.formula match {
      case Imply(_, Refinement(Compose(a1,b1),Compose(a2,b2))) => (a1, b1, a2, b2)
      case _ => throw new Exception(s"Expected axiom of form a1;b1;=<a2;b2; -> ... but found ${axiom.formula}")
    }

    val (a1Repl, b1Repl, a2Repl, b2Repl) = s(pos) match {
      case Refinement(Compose(a1,b1),Compose(a2,b2)) => (a1,b1,a2,b2)
      case _ => throw new Exception(s"Expected program refinement formula but found ${s(pos).prettyString}")
    }

    val axiomInstance = USubst(a1 ~> a1Repl :: b1 ~> b1Repl :: a2 ~> a2Repl :: b2 ~> b2Repl :: Nil)(axiom.provable)

    HilbertCalculus.CEat(axiomInstance)(pos) & TactixLibrary.andR(pos)
  })

  lazy val refineAssignAny = HilbertCalculus.byUS("refine :=*") //@todo wht about in context? CB basically?

  //endregion


  //region General-purpose helpers @todo move region out of this object and into another.

  /**
    * top-level implication rewriting. Positional argument should be the position of the implication.
    * {{{
    *             *
    *           ------ close
    * |- p, q   p |- p
    * ---------------- implyL
    *    p->q |- p
    * }}}
    *
    * @todo Hide only p in the produced subgoal (|- p,q). Requires turning this into a dependent tactic and finding the
    *       position of the assumption in the succedent.
    */
  private lazy val implicationRewriting = "implicationRewriting" by ((pos: Position, sequent: Sequent) => {
    assert(pos.isAnte)

    val Imply(left,right) = sequent.ante(pos.index0) //the implication
    val implicantPos     = TacticHelper.findInSuccedent(right, sequent).getOrElse(
        throw new Exception(s"Expected to find ${right} in the succedent of ${sequent.prettyString}"))

    PartialTactic(TactixLibrary.implyL(pos) <(
      PartialTactic(
        DebuggingTactics.assert(s => s.succ(implicantPos.index0) == right, s"Expected implicand at position ${implicantPos}") &
        DebuggingTactics.assert(s => s.succ.length >= 2, "Expected succ length >= 2") &
        TactixLibrary.hideR(implicantPos)
      ),
      TactixLibrary.close
      ))
  })

  //endregion

  //region Contextual rewriting

  /**
    * CP(pos) at the indicated position within an equivalence reduces contextual equivalence `C{left}<->C{right}`to argument program equivalence `left == right`.
    * {{{
    *       a == b
    *   --------------- CP
    *    C{a} <-> C{b}
    * }}}
    * Part of the differential dynamic logic Hilbert calculus.
    *
    * @param inExpr the position *within* the two sides of the equivalence at which the context DotProgram occurs.*/
  def CP(inExpr: PosInExpr) = HilbertCalculus.CP(inExpr)

  /**
    * {{{
    *            *
    *   ----------------------
    *          a == b                    C{b}
    *   ----------------------    --------------------
    *       C{a} == C{b}          C{a} == C{b} |- C{a}
    *   ----------------------------------------------------
    *                  |- C{a}
    * }}}
    */
  def contextualProgramEquiv = ??? //@todo

  /**
    * Simplifies a sequent by rewriting a program at a given sub-position in a sequent.
    * I.e., rewrites
    *     G |- D, ctx{a}, D'
    * into
    *     G |- D, D', ctx{b}
    * where equiv is a proof of a == b. @todo fix positioning awkwardness.
    * @todo Write a wrapper that finds the position automatically.
    * @todo Bellerophon parser improvements so that unification can be used instead of position hacking.
    *
    * Ex:
    * {{{
    *      *
    *   -------- equiv        -------
    *     a==b                 [b;]p
    *   ----------------    -------------------------
    *   [a;]p <-> [b;]p     [a;]p <-> [b;]p |- [a;]p
    *   ----------------------------------------------
    *   [a;]p
    * }}}
    * @note untested for rules with extra antecedented or succedents.
    *
    * @param equiv The tactic that will prove a==b
    */
  def useEquivAt(equiv: BelleExpr, b: Program) = s"programEquivAt('${equiv.prettyString}', {`${b.prettyString}`})" by((pos: Position, s: Sequent) => {
//    assert(s.ante.length == 0 && s.succ.length == 1, "Expected sequent of form |- G but.")

    import Augmentors._
    val (ctx, a) = s.at(pos)
    TactixLibrary.cut(Equiv(ctx(a), ctx(b))) <(
      rewriteByEquiv('Llast) & DebuggingTactics.assert(s => s.succ.last == ctx(b), "Remaining goal should be exaclty ctx(b)") partial,
      TactixLibrary.cohide('Rlast) & CP(pos.inExpr) & equiv & DebuggingTactics.assertProved
    ) partial
  })

  /**
    * {{{
    *                 |- b
    *             --------------
    *              !a |- a, b
    *             --------------
    *    *         !a, !b |- a
    * --------    --------------
    * a&b |- a    !a&!b   |- a
    * ----------------
    *   a<->b |- a
    * }}}
    */
  private lazy val rewriteByEquiv = "rewriteByEquiv" by ((equivPos: Position, s: Sequent) => {
    import Augmentors._
    val Equiv(l,r) = s(equivPos)
    val idx = s.succ.indexOf(l)
    assert(idx != -1, s"${l} should exist in succedent of ${s}")
    val succPos = SuccPos(idx)
    assert(s.at(succPos)._2 == l, s"Expected ${l} at ${succPos} but found ${s.at(succPos)}")

    TactixLibrary.equivL(equivPos) <(
      TactixLibrary.andL(equivPos) & TactixLibrary.close & DebuggingTactics.assertProved,
      PartialTactic(
        TactixLibrary.andL(equivPos) & // !p & !q |- D, p, D'
        TactixLibrary.hideR(succPos) & // !p & !q |- D, D'
        TactixLibrary.notL('Llast) &   // !p      |- D, D', q //@todo fix placement so that q takes place of p.
        TactixLibrary.hideL(equivPos)  //         |- D, D', q
      )
    ) partial
  })
  //endregion

}
