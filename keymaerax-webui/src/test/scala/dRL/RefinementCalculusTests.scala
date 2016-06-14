/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package dRL

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import scala.collection.immutable

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
    val result = proveBy(f,t)

    //provable should have the correct shape.
    result.subgoals.length shouldBe 2
    result.subgoals(0).ante.length shouldBe 0
    result.subgoals(0).succ.length shouldBe 1
    result.subgoals(1).ante.length shouldBe 0
    result.subgoals(1).succ.length shouldBe 1

    result.subgoals.map(_.succ(0)) shouldBe immutable.IndexedSeq("(a; =< b;)".asFormula, "(b; =< a;)".asFormula)
  }})}

  it should "produce correct us instance from an equality assumption." in {withMathematica({implicit qeTool => {
    val f = "(x:=1; == x:=2;)".asFormula
    val t = RefinementCalculus.refineAntisymRule('R)
    val result = proveBy(f,t)

    //provable should have the correct shape.
    result.subgoals.length shouldBe 2
    result.subgoals(0).ante.length shouldBe 0
    result.subgoals(0).succ.length shouldBe 1
    result.subgoals(1).ante.length shouldBe 0
    result.subgoals(1).succ.length shouldBe 1

    result.subgoals.map(_.succ(0)) shouldBe immutable.IndexedSeq("(x:=1; =< x:=2;)".asFormula, "(x:=2; =< x:=1;)".asFormula)
  }})}

  "refine unloop" should "proof itself" in {withMathematica(implicit qetool => {
    val f = "({a;}* =< {b;}*) <- [{a;}*]({a;}* =< {b;}*)".asFormula
    proveBy(f, RefinementCalculus.refineUnloop) shouldBe 'proved
  })}

  it should "prove a subst on itself" in {withMathematica({implicit qeTool => {
    val f = "({g;}* =< {d;}*) <- [{g;}*]({g;}* =< {d;}*)".asFormula
    proveBy(f, RefinementCalculus.refineUnloop) shouldBe 'proved
  }})}

  it should "produce correct subgoals" in {withMathematica(implicit qeTool => {
    val f = "({g;}* =< {d;}*)".asFormula
    val t = RefinementCalculus.refineUnloopRule('R)
    val result = proveBy(f,t)

    //provable should have the correct shape.
    result.subgoals.length shouldBe 1
    result.subgoals(0).ante.length shouldBe 0
    result.subgoals(0).succ.length shouldBe 1

    result.subgoals.map(_.succ(0)) shouldBe immutable.IndexedSeq("[{g;}*]({g;}* =< {d;}*)".asFormula)
  })}


  "Paper Example 1 (natural partial order)" should "prove using the proof from the paper" ignore {withMathematica(implicit qeTool => {
    val formula = "({a;++b;}==b;) <-> (a; =< b;)".asFormula
    //@todo implement and un-ignore
  })}

  "Paper example 2" should "prove using the proof from the paper" ignore {withMathematica(implicit qeTool => {
    //@todo implement and un-ignore
  })}
}
