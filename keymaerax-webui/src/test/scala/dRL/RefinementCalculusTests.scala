/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package dRL

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.Ignore // adds .asFormula, .asProgram, .asTerm methods to String class.

/**
  * Most basic tests for some tactics in the btactics.dRL namespace.
  * @note This suite only tests that axioms behave properly, so anything that isn't asserted to be 'proved might be nonsense.
  * @author Nathan Fulton
  */
class RefinementCalculusTests extends TacticTestBase {
  "refine choice comm axiom" should "prove itself" in {withMathematica(implicit qeTool => {
    val formula = "{a; ++ b;} == {b; ++ a;}".asFormula
    val result = proveBy(formula, RefinementCalculus.refineChoiceComm)
    result shouldBe 'proved //same as result.isProved shouldBe true
  })}

  it should "prove a substitution of itself" in {withMathematica(implicit qeTool => {
    val formula = "{x:=1; ++ x:=2;} == {x:=2; ++ x:=1;}".asFormula
    val result = proveBy(formula, RefinementCalculus.refineChoiceComm)
    result shouldBe 'proved //same as result.isProved shouldBe true
  })}

  "refineId" should "prove x:=1; =< x:=1;" in {
    val formula = "{x:=1;} =< {x:=1;}".asFormula
    val result = proveBy(formula, RefinementCalculus.refineId)
    result shouldBe 'proved
  }

  "boxRefine" should "prove [x:=1;]p(x) by refinement to x:=1" in {withMathematica(implicit qeTool => {
    val formula = "[x := 1;]x=1".asFormula
    val tactic = RefinementCalculus.boxRefine("x := 1;".asProgram)(1) <(
      TactixLibrary.assignb('R) &  TactixLibrary.QE,
      RefinementCalculus.refineId
    )

    val result = proveBy(formula, tactic)
    result shouldBe 'proved
  })}

  "CP" should "prove [x:=1; ++ x:=2;]p(??) <-> [x := 2; ++ x:=1;]p(??) by refinement then revineId" in {withMathematica(implicit qeTool => {
    val formula = "[{x:=1; ++ x:=2;}]p(??) <-> [{x:=2; ++ x:=1;}]p(??)".asFormula
    import Augmentors._
    formula.at(PosInExpr(0 :: 0 :: Nil))._2 shouldBe "{x:=1; ++ x:=2;}".asProgram

    val tactic = RefinementCalculus.CP(PosInExpr(0 :: Nil)) & RefinementCalculus.refineChoiceComm
    val result = proveBy(formula, tactic)
    result shouldBe 'proved
  })}

  "refine antisym" should "prove itself" in {withMathematica(implicit qetool => {
    val f = "(a; == b;) <- ((a; =< b;) & (b; =< a;))".asFormula
    proveBy(f, RefinementCalculus.refineAntisym) shouldBe 'proved
  })}

  it should "prove a subst on itself" in {withMathematica({implicit qeTool => {
    val f = "(g; == d;) <- ((g; =< d;) & (d; =< g;))".asFormula
    proveBy(f, RefinementCalculus.refineAntisym) shouldBe 'proved
  }})}

  it should "produce correct from an equality assumption." in {withMathematica({implicit qeTool => {
    val f = "(a; == b;)".asFormula
    val t = RefinementCalculus.refineAntisymRule('R)

    proveBy(f,t).subgoals(0).succ(0) shouldBe "((a; =< b;)&(b; =< a;))".asFormula
  }})}

  it should "produce correct us instance from an equality assumption." in {withMathematica({implicit qeTool => {
    val f = "(x:=1; == x:=2;)".asFormula
    val t = RefinementCalculus.refineAntisymRule('R)

    proveBy(f,t).subgoals(0).succ(0) shouldBe "((x:=1; =< x:=2;)&(x:=2; =< x:=1;))".asFormula
  }})}

  "Paper Example 1 (natural partial order)" should "prove using the proof from the paper" ignore {withMathematica(implicit qeTool => {
    val formula = "({a;++b;}==b;) <-> (a; =< b;)".asFormula
    //@todo implement and un-ignore
  })}

  "Paper example 2" should "prove using the proof from the paper" ignore {withMathematica(implicit qeTool => {
    //@todo implement and un-ignore
  })}
}
