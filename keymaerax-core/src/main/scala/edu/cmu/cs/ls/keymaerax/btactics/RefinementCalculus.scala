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
     * @todo pretty sure we have a better way of doing this but can't find it using grep ATM.
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

  /** Attempts to automatically prove that a =< b by applying idempotent semiring axioms.
    *
    * @todo come up with a good tactic modulo odes(/loops?) based on a KAT DP?
    */
  lazy val proveRefinement: DependentPositionTactic = ???

  /**
    * Proves
    * {{{
    *   a; =< a;
    * }}}
    */
  lazy val refineId : BelleExpr = "refineId" by HilbertCalculus.byUS("refine id")

  /**
    * Proves
    * {{{
    *   {a; ++ b;} == {b; ++ a;}
    * }}}
    */
  lazy val refineChoiceComm : BelleExpr = "refineChoiceComm" by HilbertCalculus.byUS("refine choice comm")
  //@todo add a tactic that rewrites {a; ++ b;} to {b; ++ a;} in a context.

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

  //region Contextual rewriting @note maybe these should be moved into UnifyUSCalculus

  def CP(inExpr: PosInExpr) = HilbertCalculus.CP(inExpr)

  //endregion

}
