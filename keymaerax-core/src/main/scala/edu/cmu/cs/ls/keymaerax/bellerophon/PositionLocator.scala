package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.tactics._

////////////////////////////////////////////////////////////////////////////////////////////////////
// Positions
////////////////////////////////////////////////////////////////////////////////////////////////////

object PositionConverter {
  /** Converts signed positions to position data structures. */
  def convertPos(seqIdx: Int, inExpr: List[Int] = Nil): Position = {
    require(seqIdx != 0, "Sequent index must be strictly negative (antecedent) or strictly positive (succedent)")
    if (seqIdx < 0) new AntePosition(-seqIdx - 1, PosInExpr(inExpr))
    else new SuccPosition(seqIdx - 1, PosInExpr(inExpr))
  }

  private[bellerophon] def convertPos(p: edu.cmu.cs.ls.keymaerax.core.SeqPos) : Position = if (p.isAnte) new AntePosition(p.getIndex, HereP) else new SuccPosition(p.getIndex, HereP)
}


/** Locates positions */
sealed trait PositionLocator {
  def prettyString: String
}

/** Locates the formula at the specified fixed position. */
case class Fixed private[keymaerax] (pos: Position, shape: Option[Formula] = None, exact: Boolean = true) extends PositionLocator {
  override def prettyString: String = pos.prettyString
}
object Fixed {
  def apply(seqPos: Int, inExpr: List[Int], shape: Option[Formula], exact: Boolean): Fixed = new Fixed(PositionConverter.convertPos(seqPos, inExpr), shape, exact)
  def apply(seqPos: Int, inExpr: List[Int], shape: Option[Formula]): Fixed = new Fixed(PositionConverter.convertPos(seqPos, inExpr), shape)
  def apply(seqPos: Int, inExpr: List[Int]): Fixed = new Fixed(PositionConverter.convertPos(seqPos, inExpr))
  def apply(seqPos: Int): Fixed = new Fixed(PositionConverter.convertPos(seqPos, Nil))
}

/** Locates the first applicable position that matches shape (exactly or unifiably) at or after start of goal. */
case class Find(goal: Int, shape: Option[Formula], start: Position, exact: Boolean = true) extends PositionLocator {
  override def prettyString: String = "'_"
}

/** Locates the last position in the antecedent. */
case class LastAnte(goal: Int) extends PositionLocator {
  override def prettyString: String ="'Llast"
}

/** Locates the last position in the succedent. */
case class LastSucc(goal: Int) extends PositionLocator {
  override def prettyString: String ="'Rlast"
}

///**
//  * Abstract positions are either actual positions, or else indicate that the tactic should point back to a position
//  * that was generated by a previous tactic.
//  *
//  * Example:
//  * {{{
//  *   AndR(SuccPos(2)) <(
//  *     ImplyR(GeneratedPosition()) & TrivialCloser,
//  *     ImplyR(GeneratedPosition()) & TrivialCloser
//  *   )
//  * }}}
//  *
//  * is equivalent to:
//  *
//  * {{{
//  *   AndR(SuccPos(2)) <(
//  *     ImplyR(SuccPos(2)) & ...,
//  *     ImplyR(SuccPos(2)) & ...
//  *   )
//  * }}}
//  *
//  * @todo Not currently using these; one thing at at a time.
//  */
//sealed trait AbstractPosition
//case class AbsolutePosition(p : Position) extends AbstractPosition
//case class GeneratedPosition()              extends AbstractPosition
//


