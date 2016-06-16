/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package dRL

import edu.cmu.cs.ls.keymaerax.bellerophon.{PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.{RefinementCalculus, _}
import edu.cmu.cs.ls.keymaerax.core.{ProgramConst, Provable, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable

/**
  * Most basic tests for some tactics in the btactics.dRL namespace.
  *
  * @note This suite only tests that axioms behave properly, so anything that isn't asserted to be 'proved might be nonsense.
  * @author Nathan Fulton
  */
class RefinementCalculusTests extends TacticTestBase {
  "refine choice comm axiom" should "prove itself" in {
    val formula = "{a; ++ b;} == {b; ++ a;}".asFormula
    val result = proveBy(formula, RefinementCalculus.refineChoiceComm)
    result shouldBe 'proved //same as result.isProved shouldBe true
  }

  it should "prove a substitution of itself" in {
    val formula = "{x:=1; ++ x:=2;} == {x:=2; ++ x:=1;}".asFormula
    val result = proveBy(formula, RefinementCalculus.refineChoiceComm)
    result shouldBe 'proved //same as result.isProved shouldBe true
  }

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

  "CP" should "prove [x:=1; ++ x:=2;]p(??) <-> [x := 2; ++ x:=1;]p(??) by refinement then revineId" in {
    val formula = "[{x:=1; ++ x:=2;}]p(??) <-> [{x:=2; ++ x:=1;}]p(??)".asFormula
    import Augmentors._
    formula.at(PosInExpr(0 :: 0 :: Nil))._2 shouldBe "{x:=1; ++ x:=2;}".asProgram

    val tactic = RefinementCalculus.CP(PosInExpr(0 :: Nil)) & RefinementCalculus.refineChoiceComm
    val result = proveBy(formula, tactic)
    result shouldBe 'proved
  }

  "CPE" should "work on x:=1; a; x:=2;" in {
    val formula = "{x:=1; a; x:=2;} == {x:=1; a; x:=2;}".asFormula
    val tactic = RefinementCalculus.CP(PosInExpr(1 :: 0 :: Nil)) & RefinementCalculus.refineTrivialCloser & DebuggingTactics.assertProved
    proveBy(formula, tactic) shouldBe 'proved
  }

  //@note this currently does not work because of problems in the core... but it should eventually work.
  ignore should "work it an arbitrary context" in {
    val formula = "ctx(a;) == ctx(a;)".asFormula
    import Augmentors._
    formula.at(PosInExpr(0 :: 1 :: Nil))._2 shouldBe "a;".asProgram
    val tactic = RefinementCalculus.CP(PosInExpr(0 :: 1 :: Nil)) & RefinementCalculus.refineTrivialCloser & DebuggingTactics.assertProved
    proveBy(formula, tactic) shouldBe 'proved
  }

  "useEquivAt" should "work" in {
    val formula = "q() -> [x:=1; ?true;]p()".asFormula
    val t = RefinementCalculus.useEquivAt(RefinementCalculus.composeIdR, "x:=1;".asProgram)(SuccPosition(1, 1 :: 0 :: Nil))

    val result = proveBy(formula, t)
    result.subgoals.length shouldBe 1
    result.subgoals(0).ante.length shouldBe 0
    result.subgoals(0).succ.length shouldBe 1

    result.subgoals(0).succ(0) shouldBe "q() -> [x:=1;]p()".asFormula
  }

  "refine antisym" should "prove itself" in {
    val f = "(a; == b;) <- ((a; =< b;) & (b; =< a;))".asFormula
    proveBy(f, RefinementCalculus.refineAntisym) shouldBe 'proved
  }

  it should "prove a subst on itself" in {
    val f = "(g; == d;) <- ((g; =< d;) & (d; =< g;))".asFormula
    proveBy(f, RefinementCalculus.refineAntisym) shouldBe 'proved
  }

  it should "produce correct from an equality assumption." in {
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
  }

  it should "produce correct us instance from an equality assumption." in {
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
  }

  "refine unloop" should "proof itself" in {
    val f = "({a;}* =< {b;}*) <- [{a;}*]({a;} =< {b;})".asFormula
    proveBy(f, RefinementCalculus.refineUnloop) shouldBe 'proved
  }

  it should "prove a subst on itself" in {
    val f = "({g;}* =< {d;}*) <- [{g;}*]({g;} =< {d;})".asFormula
    proveBy(f, RefinementCalculus.refineUnloop) shouldBe 'proved
  }

  it should "produce correct subgoals" in {
    val f = "({g;}* =< {d;}*)".asFormula
    val t = RefinementCalculus.refineUnloopRule('R)
    val result = proveBy(f, t)

    //provable should have the correct shape.
    result.subgoals.length shouldBe 1
    result.subgoals(0).ante.length shouldBe 0
    result.subgoals(0).succ.length shouldBe 1

    result.subgoals.map(_.succ(0)) shouldBe immutable.IndexedSeq("[{g;}*]({g;} =< {d;})".asFormula)
  }

  "refineCompose" should "prove itself" in {
    val f = "{a1;b1;} =< {a2;b2;} <- ( a1; =< a2; & [a1;](b1; =< b2;) )".asFormula
    proveBy(f, RefinementCalculus.refineCompose)
  }

  it should "prove a us of itself" in {
    val f = "{g1;d1;} =< {g2;d2;} <- ( g1; =< g2; & [g1;](d1; =< d2;) )".asFormula
    proveBy(f, RefinementCalculus.refineCompose)
  }

  "refineComposeRule" should "work" in {
    val f = "{g1;d1;} =< {g2;d2;}".asFormula
    val result = proveBy(f, RefinementCalculus.refineComposeRule('R))

    result.subgoals.length shouldBe 2
    val r1 = new Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("g1; =< g2;".asFormula))
    val r2 = new Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("[g1;](d1; =< d2;)".asFormula))
    result.subgoals(0) shouldBe r1
    result.subgoals(1) shouldBe r2
  }

  "refineAssignAny" should "prove itself" in {
    val f = "x:=t; =< x:=*;".asFormula
    proveBy(f, RefinementCalculus.refineAssignAny) shouldBe 'proved
  }

  it should "prove us of itself" in {
    val f = "{a:=blah;} =< {a:=*;}".asFormula
    proveBy(f, RefinementCalculus.refineAssignAny) shouldBe 'proved
  }

  "Paper Example 1 (natural partial order)" should "prove using the proof from the paper" ignore {withMathematica(implicit qeTool => {
    val formula = "({a;++b;}==b;) <-> (a; =< b;)".asFormula
    //@todo implement and un-ignore
  })}

  "Paper example 2" should "prove using the proof from the paper" in {
    val f = "{a; x:=t; b;}* =< {a; x:=*; b;}*".asFormula
    val t = RefinementCalculus.refineUnloopRule('R) & TactixLibrary.G & RefinementCalculus.refineComposeRule('R) <(
      HilbertCalculus.byUS("refine id") & DebuggingTactics.assertProved,
      TactixLibrary.G & RefinementCalculus.refineComposeRule('R) <(
        RefinementCalculus.refineAssignAny,
        TactixLibrary.G & HilbertCalculus.byUS("refine id") & DebuggingTactics.assertProved
      )
    )

    proveBy(f,t) shouldBe 'proved
  }

  "paper example 3" should "proof using the proof from the paper" in {
    val f = "p(t) -> (x:=t; =< {x:=*;?p(x);})".asFormula
    import Augmentors._
    println("({x:=t;?true;} =< {x:=*;?p(x);})".asFormula.at(PosInExpr(1::Nil))._1.apply("a".asProgram))
    val t = TactixLibrary.implyR('R) & HilbertCalculus.useAt("composeIdR")
//    val t = TactixLibrary.implyR('R) & TactixLibrary.cut("({x:=t;?true;} =< {x:=*;?p(x);}) <-> (x:=t; =< {x:=*;?p(x);})".asFormula) <(
//      Idioms.nil,
//      TactixLibrary.cohide('Rlast) & DebuggingTactics.debug("here", true) & RefinementCalculus.CP(PosInExpr(1 :: Nil))
//    )

    val result = proveBy(f,t)
//    result shouldBe 'proved
  }
}
