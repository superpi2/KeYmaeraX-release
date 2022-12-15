/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Exists, Forall, Formula, FuncOf, Not, Term, Variable}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.ext.{SmtLibReader, Z3Reader}
import edu.cmu.cs.ls.keymaerax.tools.qe.DefaultSMTConverter

import java.io.StringReader

class SmtLibTests extends TacticTestBase {
  /** Prefixes from [[DefaultSMTConverter]]. */
  private val VAR_PREFIX = "_v_"
  private val FUNC_PREFIX = "_f_"
  private val DIFFSYMBOL_PREFIX = "_d_"

  private object round {
    def trip(t: Formula): Formula = { roundTrip(t) shouldBe Not(t); t }
    def roundTrip(t: Formula): Formula = {
      def convertVar(v: Variable): Variable = v match {
        case bv: BaseVariable => bv.copy(name = bv.name.
          replaceAllLiterally(SmtLibReader.USCORE, "_").
          replaceAllLiterally(VAR_PREFIX, ""))
      }

      def convertFml(f: Formula): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
          case Exists(vs, p) => Right(Exists(vs.map(convertVar), convertFml(p)))
          case Forall(vs, p) => Right(Forall(vs.map(convertVar), convertFml(p)))
          case _ => Left(None)
        }
        override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] =  e match {
          case v: BaseVariable => Right(convertVar(v))
          case FuncOf(fn, args) =>
            Right(FuncOf(fn.copy(name = fn.name.
              replaceAllLiterally(SmtLibReader.USCORE, "_").
              replaceAllLiterally(FUNC_PREFIX, "")), args))
          case _ => Left(None)
        }
      }, f).get

      convertFml(SmtLibReader.readAssert(DefaultSMTConverter(t))._1)
    }
  }

  "SmtLibReader" should "read simple examples" in {
    round trip "x>=0".asFormula
    round trip "x+1>=0".asFormula
    round trip "\\exists x x>=0".asFormula
    round trip "\\forall x (x<=0|x>=0)".asFormula
  }

  "BigTestCase" should "reduce to single proof" in withMathematica { _ =>
    val input = """
      |(proof
      |(let ((?x74 (+ t1 t)))
      |(let (($x75 (>= ?x74 0.0)))
      |(let (($x119 (not $x75)))
      |(let ((?x251 (+ 20.0 (* (- 1.0) t))))
      |(let ((?x348 (+ ?x251 t)))
      |(let ((?x247 (- 20.0 t)))
      |(let ((?x142 (* (/ 1.0 10.0) v)))
      |(let ((?x139 (* (/ 1.0 10.0) 200.0)))
      |(let ((?x144 (- ?x139 ?x142)))
      |(let ((?x68 (* 10.0 t)))
      |(let ((?x237 (* (/ 1.0 10.0) ?x68)))
      |(let ((?x277 (* (- 10.0) t)))
      |(let ((?x280 (+ 200.0 ?x277)))
      |(let ((?x228 (* st ?x280)))
      |(let ((?x100 (* (- 10.0) st)))
      |(let ((?x103 (+ 10.0 ?x100)))
      |(let ((?x217 (* t ?x103)))
      |(let ((?x224 (+ ?x217 ?x228)))
      |(let (($x34 (= st 0.0)))
      |(let (($x229 (= v ?x224)))
      |(let (($x65 (>= z 0.0)))
      |(let (($x63 (>= v 0.0)))
      |(let (($x61 (>= s 0.0)))
      |(let (($x59 (>= t 0.0)))
      |(let ((?x46 (* t t)))
      |(let ((?x155 (* (- 5.0) ?x46)))
      |(let ((?x49 (* 200.0 t)))
      |(let ((?x121 (* (- 5.0) st)))
      |(let ((?x124 (+ 5.0 ?x121)))
      |(let ((?x39 (* 4000.0 s)))
      |(let ((?x134 (+ ?x39 (* t t ?x124) (* st (+ 2000.0 ?x49 ?x155)))))
      |(let (($x31 (>= t1 0.0)))
      |(let (($x29 (= (+ (* 10.0 t1) v) 200.0)))
      |(let (($x216 (and $x29 $x31 $x34 (= z ?x134) $x59 $x61 $x63 $x65 $x229)))
      |(let (($x239 (not (or (not $x216) $x75))))
      |(let ((?x41 (- 1.0 st)))
      |(let ((?x42 (* ?x41 10.0)))
      |(let ((?x71 (+ (* ?x42 t) (* st (- 200.0 ?x68)))))
      |(let ((?x56 (+ (+ ?x39 (* (/ ?x42 2.0) ?x46)) (* st (+ (- ?x49 (* 5.0 ?x46)) 2000.0)))))
      |(let (($x60 (and (and (and (and $x29 $x31) $x34) (= z ?x56)) $x59)))
      |(let (($x73 (and (and (and (and $x60 $x61) $x63) $x65) (= v ?x71))))
      |(let (($x77 (not (=> $x73 $x75))))
      |(let ((@x78 (asserted $x77)))
      |(let ((@x128 (mp @x78 (rewrite (= $x77 $x239)) $x239)))
      |(let ((@x129 (not-or-elim @x128 $x216)))
      |(let ((@x156 (and-elim @x129 $x34)))
      |(let ((@x225 (trans (monotonicity @x156 (= ?x228 (* 0.0 ?x280))) (rewrite (= (* 0.0 ?x280) 0.0)) (= ?x228 0.0))))
      |(let ((@x176 (trans (monotonicity @x156 (= ?x100 (* (- 10.0) 0.0))) (rewrite (= (* (- 10.0) 0.0) 0.0)) (= ?x100 0.0))))
      |(let ((@x200 (trans (monotonicity @x176 (= ?x103 (+ 10.0 0.0))) (rewrite (= (+ 10.0 0.0) 10.0)) (= ?x103 10.0))))
      |(let ((@x208 (trans (monotonicity @x200 (= ?x217 (* t 10.0))) (rewrite (= (* t 10.0) ?x68)) (= ?x217 ?x68))))
      |(let ((@x226 (trans (monotonicity @x208 @x225 (= ?x224 (+ ?x68 0.0))) (rewrite (= (+ ?x68 0.0) ?x68)) (= ?x224 ?x68))))
      |(let ((@x241 (monotonicity (trans (and-elim @x129 $x229) @x226 (= v ?x68)) (= ?x142 ?x237))))
      |(let ((@x246 (trans @x241 (rewrite (= ?x237 t)) (= ?x142 t))))
      |(let ((@x255 (trans (monotonicity (rewrite (= ?x139 20.0)) @x246 (= ?x144 ?x247)) (rewrite (= ?x247 ?x251)) (= ?x144 ?x251))))
      |(let (($x148 (= t1 ?x144)))
      |(let ((@x257 (trans (mp (and-elim @x129 $x29) (rewrite (= $x29 $x148)) $x148) @x255 (= t1 ?x251))))
      |(let ((@x354 (trans (monotonicity @x257 (= ?x74 ?x348)) (rewrite (= ?x348 20.0)) (= ?x74 20.0))))
      |(let ((@x361 (trans (monotonicity @x354 (= $x75 (>= 20.0 0.0))) (rewrite (= (>= 20.0 0.0) true)) (= $x75 true))))
      |(let ((@x368 (trans (monotonicity @x361 (= $x119 (not true))) (rewrite (= (not true) false)) (= $x119 false))))
      |(mp (not-or-elim @x128 $x119) @x368 false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))""".stripMargin
    /*
    val result = Z3Reader.read(new StringReader(input))
    result shouldBe "something"
    */
//    val lexer = new smtlib.lexer.Lexer(new StringReader(input))
//    val parser = new smtlib.parser.Parser(lexer)
//    val sExpr = parser.parseSExpr
//    print(sExpr)

     val proof = Z3Reader.read(new StringReader(input))
     print(proof)
  }

  "SmallTestCase" should "reduce to single proof" in withMathematica { _ =>
    val input = """
      |((proof
      |(mp (asserted (= a (not a))) (rewrite (= (= a (not a)) false)) false)))
      |""".stripMargin
    /*
    val result = Z3Reader.read(new StringReader(input))
    result shouldBe "something"
    */
    //    val lexer = new smtlib.lexer.Lexer(new StringReader(input))
    //    val parser = new smtlib.parser.Parser(lexer)
    //    val sExpr = parser.parseSExpr
    //    print(sExpr)

    val proof = Z3Reader.read(new StringReader(input))
    print(proof)
  }
}
