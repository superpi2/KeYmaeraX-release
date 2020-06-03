package edu.cmu.cs.ls.keymaerax.macros

import scala.annotation.StaticAnnotation
import scala.collection.immutable.Nil
import scala.language.experimental.macros
import scala.reflect.macros.{Universe, whitebox}
import AnnotationCommon._

/**
* @param names Display names to render in the user interface.
* @param inputs Display input information for non-positioning arguments, e.g., "C:Formula" for cut.
*               Arguments are separated with ;; and allowed fresh variables are given in square brackets, for example
*               E[y,x,y']:Formula;; P[y]:Formula are the arguments to tactic dG.
*               By default, this argument is inferred from the argument types and names of the annotated [[def]].
*               Use this argument when you want customized display on the UI or when there are allowedFresh variables.
 *              Supported types: Expression, Formula, Term, Variable, Number, String, Substitution, List[], Option[]
* @param premises String of premises when (if) the tactic is displayed like a rule on the UI.
*                 For tactics with (non-position) inputs, the premises or conclusion must mention each input.
*                 The name of each input is given in [[inputs]], which may be generated from the [[def]].
*                 Premises are separated by ;; and each premise is optionally a sequent.  "P;; A, B |- C" specifies two
*                 premises, the latter of which is a sequent with two assumptions. An asterisk "*" indicates a tactic that
*                 closes a branch.
* @param conclusion Conclusion of rule displayed on UI. Axiom-like tactics have a conclusion and no premises.
 *                  Tactics with premises must have conclusions.
*                   For tactics with (non-position) inputs, the premises or conclusion must mention each input.
*                   The name of each input is given in [[inputs]], which may be generated from the [[def]].
*                   Sequent syntax is optionally supported:   A, B |- C, D
* @param displayLevel Where to show the tactic: "internal" (not on UI at all), "browse", "menu", "all" (on UI everywhere)
* @TODO [[needsTool]] might be obsolete
* @param needsTool Does the tactic use tools such as QE and ODE solving? Usually not necessary.
* @param needsGenerator Does the tactic use invariant formula generators such as the @invariant annotation in .kyx files?
 *                       Used for a small number of tactics such as master.
* @param revealInternalSteps Does the Web UI allow stepping inside this tactic?
*/
class Tactic(val names: Any = false, /* false is a sigil value, user value should be string, strings, or displayinfo*/
             val premises: String = "",
             val conclusion: String = "",
             val displayLevel: String = "internal",
             val needsTool: Boolean = false,
             val needsGenerator: Boolean = false,
             val revealInternalSteps: Boolean = false,
             val inputs:String = ""
           ) extends StaticAnnotation {
    // Annotation is implemented a macro; this is a necessary, reserved magic invocation which says Tactic.impl is the macro body
    def macroTransform(annottees: Any*): Any = macro TacticImpl.apply
}

class TacticImpl(val c: whitebox.Context) {
  import c.universe._
  private trait PosArgs
  private case class OnePos(posName: ValDef, seqName: Option[ValDef]) extends PosArgs
  private case class TwoPos(provableName: ValDef, pos1Name: ValDef, pos2Name: ValDef) extends PosArgs
  private case class NoPos() extends PosArgs
  // Would just use PosInExpr but can't pull in core
  def apply(annottees: c.Expr[Any]*): c.Expr[Any] = {
    val paramNames = List("names", "premises", "conclusion", "displayLevel", "needsTool", "needsGenerator", "revealInternalSteps", "inputs")
    // Macro library does not allow directly passing arguments from annotation constructor to macro implementation.
    // Searching the prefix allows us to recover the arguments
    def getLiteral(t: Tree): String = {
      t match {
        case Literal(Constant(s: String)) => s
        case t => c.abort(c.enclosingPosition, "Expected string literal, got: " + t)
      }
    }
    def getBoolLiteral(t: Tree): Boolean = {
      t match {
        case Literal(Constant(s: Boolean)) => s
        case t => c.abort(c.enclosingPosition, "Expected string literal, got: " + t)
      }
    }
    def paramify(tn: TermName, params: Seq[Tree]): (DisplayInfo, List[ArgInfo], String, Boolean, Boolean, Boolean) = {
      val defaultMap: Map[String, Tree] = Map(
        "names"    -> Literal(Constant(false)),
        "premises" -> Literal(Constant("")),
        "conclusion" -> Literal(Constant("")),
        "displayLevel" -> Literal(Constant("internal")),
        "needsTool" -> Literal(Constant(false)),
        "needsGenerator" -> Literal(Constant(false)),
        "revealInternalSteps" -> Literal(Constant(false)),
        "inputs" -> Literal(Constant(""))
      )
      val (idx, _wereNamed, paramMap) = params.foldLeft((0, false, defaultMap))({case (acc, x) => foldParams(c, paramNames)(acc, x)})
      val (inputString,  displayLevel, premisesString, conclusionString, needsTool, needsGenerator, revealInternal) =
        (getLiteral(paramMap("inputs")),
          getLiteral(paramMap("displayLevel")), getLiteral(paramMap("premises")), getLiteral(paramMap("conclusion")),
          getBoolLiteral(paramMap("needsTool")), getBoolLiteral(paramMap("needsGenerator")), getBoolLiteral(paramMap("revealInternalSteps")))
      val inputs: List[ArgInfo] = parseAIs(inputString)(c)
      val simpleDisplay = paramMap("names") match {
        case q"""(${Literal(Constant(sl: String))}, ${Literal(Constant(sr: String))})""" => SimpleDisplayInfo(sl, sr)
        case Literal(Constant(s: String)) => SimpleDisplayInfo(s, s)
        case Literal(Constant(false)) => {
          val s = tn.decodedName.toString
          SimpleDisplayInfo(s, s)
        }
        //case sdi: SimpleDisplayInfo => sdi
        case di => c.abort(c.enclosingPosition, "@Tactic expected names: String or names: (String, String) or names: SimpleDisplayInfo, got: " + di)
      }
      val displayInfo = (inputs, premisesString, conclusionString) match {
        case (Nil, "", "") => simpleDisplay
        case (Nil, "", concl) if concl != "" => AxiomDisplayInfo(simpleDisplay, concl)
        case (ins, prem, concl) if concl != "" => InputAxiomDisplayInfo(simpleDisplay, concl, inputs)
        case (ins, prem, concl) if concl != "" && prem != "" =>
          val (prem, conc) = (parseSequents(premisesString)(c), parseSequent(conclusionString)(c))
          RuleDisplayInfo(simpleDisplay, conc, prem)
        case _ => c.abort(c.enclosingPosition, "Unsupported argument combination for @Tactic: If premises or inputs are given, conclusion must be given")
      }
      (displayInfo, inputs, displayLevel, needsTool, needsGenerator, revealInternal)
    }
    def getParams (tn: TermName): (DisplayInfo, List[ArgInfo], String, Boolean, Boolean, Boolean) = {
        c.prefix.tree match {
        case q"new $annotation(..$params)" => paramify(tn, params)
        case q"new $annotation()" => paramify(tn, Nil)
        case e => c.abort(c.enclosingPosition, "Excepted @Tactic(args), got: " + e)
      }
    }
    // Return type of tactic definition should be BelleExpr
    def isTactic(tRet: Tree): Boolean = {
      tRet match {
        case tq"DependentTactic" | tq"DependentPositionTactic" | tq"InputPositionTactic"
             | tq"BuiltInTwoPositionTactic" | tq"InputTwoPositionTactic" => true
        case _ => false
      }
    }
    // Scrape position argument info from declaration
    def getPositioning(params: Seq[Tree]): PosArgs = {
      params.toList match {
        // ValDef is also used for argument specifications
        case Nil => NoPos()
        case (posDef: ValDef) :: Nil =>
          posDef.tpt match {
            case (tq"Position") => OnePos(posDef, None)
            case params => c.abort(c.enclosingPosition, "Positioning arguments must be unit, Position, (Position, Sequent), or (ProvableSig, Position, Position), got: " + params)
          }
        case (posDef: ValDef) :: (seqDef: ValDef) :: Nil  =>
          (posDef.tpt, seqDef.tpt) match {
            case (tq"Position", tq"Sequent") => OnePos(posDef, Some(seqDef))
            case params => c.abort(c.enclosingPosition, "Positioning arguments must be unit, Position, (Position, Sequent), or (ProvableSig, Position, Position), got: " + params)
          }
        case (provableDef: ValDef) :: (pos1Def: ValDef) :: (pos2Def: ValDef) :: Nil  =>
          (provableDef.tpt, pos1Def.tpt, pos2Def.tpt) match {
            case (tq"ProvableSig", tq"Position", tq"Position") => TwoPos(provableDef, pos1Def, pos2Def)
            case params => c.abort(c.enclosingPosition, "Positioning arguments must be unit, Position, (Position, Sequent), or (ProvableSig, Position, Position), got: " + params)
          }
        case params => c.abort(c.enclosingPosition, "Positioning arguments must be unit, Position, (Position, Sequent), or (ProvableSig, Position, Position), got: " + params.map(_.getClass).mkString(","))
      }
    }
    // Scrape argument info from declaration
    def getInput(param: c.universe.Tree): ArgInfo = {
      param match {
        case v: ValDef =>
          v.tpt match {
            case tq"""Formula""" => FormulaArg(v.name.decodedName.toString)
            case tq"""Expression""" => new ExpressionArg(v.name.decodedName.toString)
            case tq"""Term""" => new TermArg(v.name.decodedName.toString)
            case tq"""Number""" => NumberArg(v.name.decodedName.toString)
            case tq"""Variable""" => VariableArg(v.name.decodedName.toString)
            case tq"""String""" => StringArg(v.name.decodedName.toString)
            case tq"""Substitution""" => SubstitutionArg(v.name.decodedName.toString)
            case tq"""Option[$t]""" => new OptionArg(getInput(t))
            case tq"""List[$t]""" => new ListArg(v.name.decodedName.toString, getInput(t).name)
          }
      }
    }
    def getInputs(params: Seq[c.universe.Tree]): List[ArgInfo] = {
      params.toList.map(getInput)
    }
    // Scala types corresponding to tactic inputs
    // @TODO rename
    def typeName(ai: ArgInfo): Tree = {
      ai match {
        case _: FormulaArg => tq"edu.cmu.cs.ls.keymaerax.core.Formula"
        case _: StringArg => tq"String"
        case _: NumberArg => tq"edu.cmu.cs.ls.keymaerax.core.Number"
        case _: VariableArg => tq"edu.cmu.cs.ls.keymaerax.core.Variable"
        case _: TermArg => tq"edu.cmu.cs.ls.keymaerax.core.Term"
        case _: SubstitutionArg => tq"edu.cmu.cs.ls.keymaerax.core.Subst"
        case _: ExpressionArg => tq"edu.cmu.cs.ls.keymaerax.core.Expression"
      }
    }
    // Type and term ASTs which wrap acc in position and/or input arguments as anonymous lambdas
    def argue(funName: String, acc: Tree, pos: PosArgs, args: List[ArgInfo]): (Tree, Tree, Tree) = {
      val funStr = Literal(Constant(funName))
      val argExpr = args match {
        case Nil => q"Nil"
        case _ => args.foldRight[Tree](q"Nil")({case (ai, acc) => q"${ai.name} :: $acc"})
      }
      val base: (Tree, Tree) =
        pos match {
          case NoPos() =>
              if(args.isEmpty)
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by($funStr, $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentTactic")
              else
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.InputTactic")
          case OnePos(pname, None) =>
            if(args.isEmpty)
              (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($pname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic")
            else
              (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, ($pname) =>  $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic")
          case OnePos(pname, Some(sname)) =>
              if(args.isEmpty)
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by(($pname, $sname) =>  $acc)""",tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic")
              else
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, ($pname, $sname) =>  $acc)""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic")
          case TwoPos(provable, pos1, pos2) =>
              if(args.isEmpty)
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).by((($provable, $pos1, $pos2) =>  $acc))""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInTwoPositionTactic")
              else
                (q"""new edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory ($funStr).byWithInputs($argExpr, (($provable, $pos1, $pos2) =>  $acc))""", tq"edu.cmu.cs.ls.keymaerax.bellerophon.AppliedBuiltInTwoPositionTactic")
      }
      def aiToVal(ai: ArgInfo): ValDef = {
        val name = ai match {
          case a: VariableArg => a.name case a: FormulaArg => a.name case n: NumberArg => n.name
          case a: StringArg => a.name case a: TermArg => a.name case a: SubstitutionArg => a.name
          case a: ExpressionArg => a.name
        }
        val argTy = typeName(ai)
        ValDef(Modifiers(), name, tq"""$argTy""", EmptyTree)
      }
      val (curried, typeTree) = args.foldRight[(Tree, Tree)](base)({case (arg, (acc, accTy)) =>
        val argTy = typeName(arg)
        val funTy = tq"""edu.cmu.cs.ls.keymaerax.macros.TypedFunc[$argTy, $accTy]"""
        val vd = aiToVal(arg)
        if(vd.rhs.nonEmpty)
          c.abort(c.enclosingPosition, "Nonempty val")
        val term =
          q"""(($vd) => $acc): $funTy"""
        (term, funTy)})
      val argSeq: Seq[ValDef] = args.map(aiToVal)
      val argTySeq: Seq[Tree] = argSeq.map(_.tpt)
      val (uncurried, uncurriedType) =
        if(argSeq.isEmpty) base
        else (q"((..$argSeq) => ${base._1})", tq"""(..$argTySeq => ${base._2})""")
      (curried, uncurried, uncurriedType)
    }
    def assemble(mods: Modifiers, codeName: TermName, inArgs: Seq[c.universe.Tree], positions: PosArgs, rhs: Tree): c.Expr[Nothing] = {
      val (display, _argInfoAnnotation, displayLevel, needsTool, needsGenerator, revealInternalSteps) = getParams(codeName)
      val inputs = getInputs(inArgs)
      val underlyingCodeName = codeName.decodedName.toString
      if (codeName.toString.exists(c => c =='\"'))
        c.abort(c.enclosingPosition, "Identifier " + codeName + " must not contain escape characters")
      // AST for literal strings for the names
      val codeString = Literal(Constant(codeName.decodedName.toString))
      val (curriedTermTree, uncurriedTermTree, uncurriedType) = argue(underlyingCodeName, rhs, positions, inputs)
      val expr = q"""((_: Unit) => ($curriedTermTree))"""
      // @TODO: Add to info constructors
      val dispLvl = displayLevel match {case "internal" => 'internal case "browse" => 'browse case "menu" => 'menu case "all" => 'all
      case s => c.abort(c.enclosingPosition, "Unknown display level " + s)}
      val (info, rhsType) = (inputs, positions) match {
        case (Nil, _: NoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.TacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.DependentTactic""")
        case (Nil, _: OnePos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.PositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic""")
        case (Nil, _: TwoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.TwoPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.BuiltInTwoPositionTactic""")
        case (_, _: NoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(inputs)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.InputTactic""")
        case (_, _: OnePos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(inputs)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator, revealInternalSteps = $revealInternalSteps)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionWithAppliedInputTactic""")
        case (_, _: TwoPos) => (q"""new edu.cmu.cs.ls.keymaerax.macros.InputTwoPositionTacticInfo(codeName = $codeString, display = ${convDI(display)(c)}, inputs = ${convAIs(inputs)(c)}, theExpr = $expr, needsTool = $needsTool, needsGenerator = $needsGenerator)""", tq"""edu.cmu.cs.ls.keymaerax.bellerophon.AppliedBuiltInTwoPositionTactic""")
      }
      // Macro cannot introduce new statements or declarations, so introduce a library call which achieves our goal of registering
      // the tactic info to the global derivation info table
      val application = q"""edu.cmu.cs.ls.keymaerax.macros.DerivationInfo.registerL($uncurriedTermTree, $info)"""
      if (inputs.isEmpty)
        c.Expr[Nothing](q"""$mods val $codeName: $uncurriedType = $application""")
      else
        c.Expr[Nothing](q"""$mods val $codeName: $uncurriedType = $application""")
    }
    annottees map (_.tree) toList match {
      // Annottee must be a val or def declaration of an tactic
      case (defDecl: DefDef) :: Nil =>
        defDecl match {
          // def has parameters for positions and/or inputs, and may have a return type
          case q"$mods def ${codeName: TermName}(..$inArgs): $tRet = ${f: Ident}($theRhs)" =>
            theRhs match {
              case q"((..$params) => $rhs)" =>
                if (f.toString != "anon")
                  c.abort(c.enclosingPosition, s"Unexpected function $f on RHS")
                if (!isTactic(tRet))
                  c.abort(c.enclosingPosition, "Invalid annottee: Expected val <tactic>: <Tactic> = <anon> ((args) => rhs)..., got: " + tRet + " " + tRet.getClass)
                val positions = getPositioning(params)
                assemble(mods, codeName, inArgs, positions, rhs)
              case t => c.abort(c.enclosingPosition, "Expected anonymous function, got:" + t)
            }
        }
      case (valDecl: ValDef) :: Nil =>
        valDecl match {
          case q"$mods val ${codeName: TermName}: $tRet = ${f: Ident}($theRhs)" =>
             theRhs match {
               case q"((..$params) => $rhs)" =>
                if (f.toString != "anon")
                  c.abort(c.enclosingPosition, s"Unexpected function $f on RHS")
                if (!isTactic(tRet))
                  c.abort(c.enclosingPosition, "Invalid annottee: Expected val <tactic>: <Tactic> = <anon> ((args) => rhs)..., got: " + tRet + " " + tRet.getClass)
                val positions = getPositioning(params)
                assemble(mods, codeName, Nil, positions, rhs)
               case t => c.abort(c.enclosingPosition, "Expected anonymous function, got:" + t)
               }
          case q"$mods val $cName: $tpt = $functionName( ..$params )" => c.abort(c.enclosingPosition, "Expected val of tactic, got:" + valDecl)
        }
      case t => c.abort(c.enclosingPosition, "Invalid annottee: Expected val or def declaration got: " + t.head + " of type: " + t.head.getClass())
    }
  }
}