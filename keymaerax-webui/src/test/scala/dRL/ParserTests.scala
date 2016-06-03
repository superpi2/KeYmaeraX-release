/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package dRL

import edu.cmu.cs.ls.keymaerax.core.{And, Refinement}
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

  //@todo x:=1; <~ x:=2; & 1=1 does not parse probably due to precedence issues.
}
