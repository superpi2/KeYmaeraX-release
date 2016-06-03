/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package dRL

import edu.cmu.cs.ls.keymaerax.btactics.{HilbertCalculus, RefinementCalculus, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._ // adds .asFormula, .asProgram, .asTerm methods to String class.

/**
  * Tests the idempotent semiring proof rules/axioms.
  *
  * @author Nathan Fulton
  */
class IdempotentSemiRingTests extends TacticTestBase {
  "refine choice comm axiom" should "prove itself" in {withMathematica(implicit qeTool => {
    val formula = "{a; ++ b;} ~~ {b; ++ a;}".asFormula
    val result = proveBy(formula, RefinementCalculus.refineChoiceComm)
    result shouldBe 'proved //same as result.isProved shouldBe true
  })}

  it should "prove a substitution of itself" in {withMathematica(implicit qeTool => {
    val formula = "{x:=1; ++ x:=2;} ~~ {x:=2; ++ x:=1;}".asFormula
    val result = proveBy(formula, RefinementCalculus.refineChoiceComm)
    result shouldBe 'proved //same as result.isProved shouldBe true
  })}
}
