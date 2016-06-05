/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package dRL

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Nathan Fulton
  */
class ParserTests extends FlatSpec with Matchers {
  "KeYmaeraX Parser" should "parse x:=1 <~ x:=1" in {
    val input = "x := 1; <~ x := 2;"
    KeYmaeraXParser(input) shouldBe Refinement("x:=1;".asProgram, "x:=2;".asProgram)
  }

  it should "parse (x:=1; <~ x:=2;) & 1=1" in {
    val input = "(x:=1; <~ x:=2;) & 1=1"
    KeYmaeraXParser(input) shouldBe And(Refinement("x:=1;".asProgram, "x:=2;".asProgram), "1=1".asFormula)
  }

  it should "parse x:=1; ~~ x:=1;" in {
    val input = "x:=1; ~~ x:=2;"
    KeYmaeraXParser(input) shouldBe ProgramEquiv("x:=1;".asProgram, "x:=2;".asProgram)
  }

  it should "parse [<~] axiom" in {
    val input = "[a;]p(??) <- ( ([b;]p(??)) & (a; <~ b;) )"
    KeYmaeraXParser(input) shouldBe Imply(And("[b;]p(??)".asFormula, "a; <~ b;".asFormula), "[a;]p(??)".asFormula)
  }

  it should "load axioms file, whcih contains many uses of both <~ and ~~" in {
    Provable.axiom //@todo not sure this does what I think it does...
  }

  it should "parse us of [<~] axiom" in {
    val f = "([a:=1;]a=1) <-> (([a:=2;]a=1)&(a:=1; <~ a:=2;))".asFormula
  }


  //@todo x:=1; <~ x:=2; & 1=1 does not parse probably due to precedence issues.
}
