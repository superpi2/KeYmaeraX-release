/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
/**
  * Uniform Renaming for KeYmaera X
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
  * @note Code Review: 2016-08-17
  */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable

/**
  * Uniformly rename all occurrences of `what` and `what'` to `repl` and `repl'` and vice versa, but clash for program constants etc.
  * Uniformly rename all occurrences of variable `what` (and its associated DifferentialSymbol `what'`) to
  * `repl` (and its associated DifferentialSymbol `repl'`) everywhere
  * and vice versa uniformly rename all occurrences of variable `repl` (and its associated DifferentialSymbol) to `what` (and `what'`).
  * Uniform renaming, thus, is a transposition.
  * @param what What variable to replace (along with its associated DifferentialSymbol).
  * @param repl The target variable to replace `what` with and vice versa.
  * @param semantic `true` to allow semantic renaming of SpaceDependent symbols,
  *                 which preserves local soundness when applied to inferences.
  * @author Andre Platzer
  * @author smitsch
  * @note soundness-critical
  * @see [[UniformRenaming]]
  * @see [[BoundRenaming]]
  * @see [[Provable.apply()]]
  */
final case class URename(what: Variable, repl: Variable, semantic: Boolean = false) extends (Expression => Expression) {
  insist(what.sort == repl.sort, "Uniform renaming only to variables of the same sort: " + this)
  //@note Unlike renaming x to z, renaming x' to z would be unsound in (x+y)'=x'+y'.
  insist(what.isInstanceOf[BaseVariable] && repl.isInstanceOf[BaseVariable], "Renaming only supports base variables: " + this)

  /** `true` for transpositions (replace `what` by `repl` and `what'` by `repl'` and, vice versa, `repl` by `what` etc) or `false` to clash upon occurrences of `repl` or `repl'`. */
  private[core] val TRANSPOSITION: Boolean = true

  override def toString: String = "URename{" + what.asString + "~>" + repl.asString + (if (semantic) " SEMANTICALLY" else "") + "}"


  /** apply this uniform renaming everywhere in an expression, resulting in an expression of the same kind. */
  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    case p: DifferentialProgram => apply(p)
    case p: Program => apply(p)
    case f: Function => throw new RenamingClashException("Renamings are not defined on an isolated Function that is not applied to arguments.", this.toString, f.asString)
  }

  /** apply this uniform renaming everywhere in a term */
  def apply(t: Term): Term = try rename(t) catch { case ex: ProverException => throw ex.inContext(t.prettyString) }

  /** apply this uniform renaming everywhere in a formula */
  def apply(f: Formula): Formula = try rename(f) catch { case ex: ProverException => throw ex.inContext(f.prettyString) }

  /** apply this uniform renaming everywhere in a program */
  def apply(p: DifferentialProgram): DifferentialProgram = try renameODE(p) catch { case ex: ProverException => throw ex.inContext(p.prettyString) }

  /** apply this uniform renaming everywhere in a program */
  def apply(p: Program): Program = try rename(p) catch { case ex: ProverException => throw ex.inContext(p.prettyString) }

  /**
    * Apply uniform renaming everywhere in the sequent.
    */
  //@note mapping apply instead of the equivalent rename makes sure the exceptions are augmented and the ensures contracts checked.
  def apply(s: Sequent): Sequent = try { Sequent(s.ante.map(apply), s.succ.map(apply))
  } catch { case ex: ProverException => throw ex.inContext(s.toString) }

  // implementation

  /** Rename a variable and/or differential symbol x
    * (that occurs in the given `context` for error reporting purposes) */
  private def renVar(x: Variable, context: Expression): Variable =
    if (x==what) repl
    else if (x==repl) if (TRANSPOSITION) what else throw new RenamingClashException("Replacement name " + repl.asString + " already occurs originally", this.toString, x.asString, context.prettyString)
    else x match {
      case DifferentialSymbol(y) => DifferentialSymbol(renVar(y, context))
      case x: BaseVariable => x
    }

  /** Rename taboo variable (and/or differential symbol) in the given space. */
  private def renSpace(space: Space): Space = space match {
    case AnyArg        => AnyArg
    case Except(taboo) => Except(renVar(taboo, taboo))
  }

  private def rename(term: Term): Term = term match {
    case x: Variable               => renVar(x, term)
    case n: Number                 => n
    case FuncOf(f:Function, theta) => FuncOf(f, rename(theta))
    case Nothing | DotTerm(_, _)   => term
    // homomorphic cases
    //@note the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeTerm => f.reapply(rename(f.left), rename(f.right))
    case Neg(e)       => Neg(rename(e))
    case Plus(l, r)   => Plus(rename(l),   rename(r))
    case Minus(l, r)  => Minus(rename(l),  rename(r))
    case Times(l, r)  => Times(rename(l),  rename(r))
    case Divide(l, r) => Divide(rename(l), rename(r))
    case Power(l, r)  => Power(rename(l),  rename(r))
    case Differential(e) => Differential(rename(e))
    // unofficial
    case Pair(l, r)   => Pair(rename(l),   rename(r))
    case UnitFunctional(f,sp,s) => if (semantic) UnitFunctional(f,renSpace(sp),s) else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: UnitFunctional " + term, this.toString, term.toString)
  }

  private def rename(formula: Formula): Formula = formula match {
    case PredOf(p, theta)   => PredOf(p, rename(theta))
    case True | False       => formula

    //@note the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeFormula => f.reapply(rename(f.left), rename(f.right))

    // pseudo-homomorphic base cases
    case Equal(l, r)        => Equal(rename(l),        rename(r))
    case NotEqual(l, r)     => NotEqual(rename(l),     rename(r))
    case GreaterEqual(l, r) => GreaterEqual(rename(l), rename(r))
    case Greater(l, r)      => Greater(rename(l),      rename(r))
    case LessEqual(l, r)    => LessEqual(rename(l),    rename(r))
    case Less(l, r)         => Less(rename(l),         rename(r))

    // homomorphic cases
    case Not(g)      => Not(rename(g))
    case And(l, r)   => And(rename(l),   rename(r))
    case Or(l, r)    => Or(rename(l),    rename(r))
    case Imply(l, r) => Imply(rename(l), rename(r))
    case Equiv(l, r) => Equiv(rename(l), rename(r))

    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(g) => DifferentialFormula(rename(g))

    case Forall(vars, g) => Forall(vars.map(x => renVar(x,formula)), rename(g))
    case Exists(vars, g) => Exists(vars.map(x => renVar(x,formula)), rename(g))

    case Box(p, g)       => Box(rename(p), rename(g))
    case Diamond(p, g)   => Diamond(rename(p), rename(g))

    case PredicationalOf(c, fml) => throw new RenamingClashException("Cannot replace semantic dependencies syntactically: Predicational " + formula, this.toString, formula.toString)
    case DotFormula              => if (semantic) DotFormula else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: DotFormula " + formula, this.toString, formula.toString)
    case UnitPredicational(p,sp) => if (semantic) UnitPredicational(p,renSpace(sp)) else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: UnitPredicational " + formula, this.toString, formula.toString)
  }

  private def rename(program: Program): Program = program match {
    case Assign(x, e)                => Assign(renVar(x,program), rename(e))
    case AssignAny(x)                => AssignAny(renVar(x,program))
    case Test(f)                     => Test(rename(f))
    case ODESystem(a, h)             => ODESystem(renameODE(a), rename(h))
    //@note This case happens for standalone uniform substitutions on differential programs such as x'=f() or c as they come up in unification for example.
    case ode: DifferentialProgram    => renameODE(ode)
    //@note the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeProgram => f.reapply(rename(f.left), rename(f.right))
    case Choice(a, b)                => Choice(rename(a), rename(b))
    case Compose(a, b)               => Compose(rename(a), rename(b))
    case Loop(a)                     => Loop(rename(a))
    case Dual(a)                     => Dual(rename(a))
    case ProgramConst(a,sp)          => if (semantic) ProgramConst(a,renSpace(sp)) else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: ProgramConstant " + a, this.toString, program.toString)
    case SystemConst(a,sp)           => if (semantic) SystemConst(a,renSpace(sp)) else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: SystemConstant " + a, this.toString, program.toString)
  }

  private def renameODE(ode: DifferentialProgram): DifferentialProgram = ode match {
    case AtomicODE(DifferentialSymbol(x), e) => AtomicODE(DifferentialSymbol(renVar(x,ode)), rename(e))
    // homomorphic cases
    case DifferentialProduct(a, b)   => DifferentialProduct(renameODE(a), renameODE(b))
    //
    case DifferentialProgramConst(c,sp) => if (semantic) DifferentialProgramConst(c,renSpace(sp)) else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: DifferentialProgramConstant " + ode, this.toString, ode.toString)
  }
}