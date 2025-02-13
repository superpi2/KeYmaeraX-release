/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, KeYmaeraXArchivePrinter, ParseException, ParsedArchiveEntry, PrettierPrintFormatProvider}

import scala.collection.immutable.{::, List, Nil}

object ArchiveEntryPrinter {
  def archiveEntry(modelInfo: ModelPOJO, tactics: List[(String, String)], withComments: Boolean): String = try {
    ArchiveParser.parser(modelInfo.keyFile) match {
      case (entry@ParsedArchiveEntry(name, _, _, _, _, _, _, _, _)) :: Nil if name == "<undefined>" =>
        new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments)(replaceInfo(entry, modelInfo.name, tactics))
      case (entry@ParsedArchiveEntry(name, _, _, _, _, _, _, _, _)) :: Nil if name != "<undefined>" =>
        new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments)(replaceInfo(entry, entry.name, tactics))
    }
  } catch {
    case _: ParseException =>
      val printedTactics = tactics.map({
        case (name, steps) =>
          s"""Tactic "$name"
             |$steps
             |End.""".stripMargin
      }).mkString("\n")
      s"""/* Model or tactics did not reparse, printed verbatim, needs manual editing */
         |
         |/* Input content */
         |${modelInfo.keyFile}
         |/* End input content */
         |
         |/* Printed tactics */
         |$printedTactics
         |/* End printed tactics */
         |""".stripMargin
  }

  private def replaceInfo(entry: ParsedArchiveEntry, entryName: String, tactics: List[(String, String)]): ParsedArchiveEntry = {
    entry.copy(name = entryName, tactics = tactics.map(e => (e._1, RequestHelper.tacticString(e._2), TactixLibrary.skip)))
  }
}