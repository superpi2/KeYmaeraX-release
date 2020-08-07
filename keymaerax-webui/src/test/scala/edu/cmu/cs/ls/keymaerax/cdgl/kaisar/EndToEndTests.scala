package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.RandomParserTests
import edu.cmu.cs.ls.keymaerax.tags._
import fastparse.Parsed.{Failure, Success}
import fastparse._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

class EndToEndTests extends TacticTestBase {

  val check: String => Formula = Kaisar.apply

  // @TODO: limit set of programVar equalities after BoxLoop...
  "full proof checker" should "check box loop" in withMathematica { _ =>
      val pfStr = "?xZero:(x >= 1); {{x := x + 1; !IS:(x >= 1) using x xZero by auto;}*} !xFin:(x>=0) using xZero by auto;"
      val ff = check(pfStr)
      ff shouldBe "[?x>=1;x_0:=x;{x_1:=x_0+1; {?x_1>=1;}^@ x_0:=x_1;}*{?x_0>=0;}^@]true".asFormula
  }

  it should "resolve simple backward state labels:" in withMathematica { _ =>
    val pfStr =
        "init: ?xZero:(x >= 1);" +
        "  !IH: (x >= x@init) by auto;" +
        "  {loop: x:=x+1;" +
        "  !step:(x >= x@loop) by auto; " +
        "  !IS:(x >= x@init) using step IH by auto;" +
        "}*" +
        "!final:(x >= 0) using xZero IH by auto;"
    val ff = check(pfStr)
    ff shouldBe "[?x>=1;{?x>=x;}^@ x_0:=x;{x_1:=x_0+1;  {?x_1>=x_0;}^@ {?x_1>=x;}^@ x_0:=x_1;}*{?x_0>=0;}^@]true".asFormula
  }

  it should "prove solution cut that requires domain constraint assumption" in withMathematica { _ =>
    val pfStr = "?tInit:(t:= 0); ?xInit:(x:= 1);  {t' = 1, x' = -1 & xRange:(x >=0) & !tRange:(t <= 1) using xInit tInit xRange by solution};"
    val ff = check(pfStr)
    ff shouldBe "[t_0:=0; x_0:= 1; {t_1 := t_0;x_1:=x_0;}{t_1' = 1, x_1' = -1 & x_1>=0}]true".asFormula
  }

  it should "prove diffcut" in withMathematica { _ =>
    val pfStr = "?yZero:(y:=0); ?xZero:(x:=1); x' = y & !dc:(x > 0) using xZero yZero by solution;"
    val ff = check(pfStr)
    ff shouldBe "[y_0:=0; x_0:=1;x_1:=x_0;{x_1' = y_0}]true".asFormula
  }

  it should "catch bad diffcut" in withMathematica { _ =>
    val pfStr = "?xZero:(x:=1); x' = -1 & !dc:(x > 0) using xZero by induction;"
    a[ProofCheckException] shouldBe thrownBy(check(pfStr))
  }

  it should "prove dc-assign" in withMathematica { _ =>
    val pfStr = "t:= 0; {t' = 1, x' = y & t := T};"
    val ff = check(pfStr)
    ff shouldBe "[t_0:= 0; {t_1 := t_0; x_0 := x;}{{t_1' = 1, x_0' = y}; ?(t_1= T);}^@]true".asFormula
  }

  it should "prove renamed dc-assign" in withMathematica { _ =>
    val pfStr = "timer:= 0; {timer' = 1, x' = y & timer := T};"
    val ff = check(pfStr)
    ff shouldBe "[timer_0:= 0; {timer_1:=timer_0;x_0:=x;}{{timer_1' = 1, x_0' = y}; ?(timer_1 = T);}^@]true".asFormula
  }

  it should "prove diamond assertion " in withMathematica { _ =>
    val pfStr = "t:= 0; {t' = 1, x' = y & t := T & !dc:(t >= 0) by induction};"
    val ff = check(pfStr)
    ff shouldBe "[t_0:=0; {t_1:=t_0;x_0:=x;}{{t_1'=1, x_0'=y & t_1>=0}; ?(t_1=T);}^@]true".asFormula
  }

  it should "prove triple induction " in withMathematica { _ =>
    val pfStr = "?xInit:(x:=0); ?yInit:(y:=0); ?zInit:(z:=0); " +
      "{x'=z, y' = 1, z' = y " +
      "& !yInv:(y >= 0) using yInit  by induction" +
      "& !zInv:(z >= 0) using zInit yInv by induction" +
      "& !xInv:(x >= 0) using xInit zInv by induction" +
      "};"
    val ff = check(pfStr)
    ff shouldBe "[x_0:=0; y_0:=0;z_0:=0;{x_1:=x_0;y_1:=y_0;z_1:=z_0;}{x_1'=z_1, y_1'=1, z_1'=y_1}]true".asFormula
  }

  it should "catch invalid dc-assign 3: wrong clock" in withMathematica { _ =>
    val pfStr = "t:= 0; {t' = 2, x' = y & t := T};"
    a[ProofCheckException] shouldBe thrownBy(check(pfStr))
  }

}
