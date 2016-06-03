/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._ //adds a "by" method to String.

/**
  * Hilbert-style uniform substitution calculus for dRL.
  * @author Nathan Fulton
  */
object RefinementCalculus {
  /**
    * Proves
    * {{{
    *   {a; ++ b;} ~~ {b; ++ a;}
    * }}}
    */
  lazy val refineChoiceComm : BelleExpr = "refineChoiceComm" by HilbertCalculus.byUS("refine choice comm")

  //@todo add a tactic that rewrites {a; ++ b;} to {b; ++ a;} in a context.
}
