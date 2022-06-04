package me.cassayre.florian.masterproject.front.printer

import lisa.kernel.proof.SequentCalculus as SC
import lisa.kernel.fol.FOL
import me.cassayre.florian.masterproject.front.*
import me.cassayre.florian.masterproject.front.parser.KernelRuleIdentifiers
import me.cassayre.florian.masterproject.front.printer.FrontPositionedPrinter
import me.cassayre.florian.masterproject.front.printer.FrontPrintStyle.{Ascii, Latex, Unicode}

object KernelPrinter {

  private case class ProofWrapper(steps: IndexedSeq[StepWrapper], imports: IndexedSeq[Sequent])
  private sealed abstract class StepWrapper {
    val name: String
    val sequent: Sequent
    val premises: Seq[Int]
    val parameters: Seq[String]
  }
  private case class NormalStepWrapper(name: String, premises: Seq[Int], sequent: Sequent, parameters: Seq[String]) extends StepWrapper
  private case class SubproofStepWrapper(name: String, proof: ProofWrapper, premises: Seq[Int]) extends StepWrapper {
    override val sequent: Sequent = proof.steps.last.sequent
    override val parameters: Seq[String] = Seq.empty
  }

  def prettyProof(scProof: lisa.kernel.proof.SCProof, style: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, explicit: Boolean = false): String = {
    val p = FrontPrintParameters(style, compact)
    val r = KernelRuleIdentifiers(p.s)
    def sequentFromKernel(s: lisa.kernel.proof.SequentCalculus.Sequent): Sequent = {
      def sorted(seq: IndexedSeq[Formula]): IndexedSeq[Formula] = seq.sortBy(_.toString)
      Sequent(sorted(s.left.toIndexedSeq.map(fromKernel)), sorted(s.right.toIndexedSeq.map(fromKernel)))
    }
    def prettyName(name: String): String = style match {
      case FrontPrintStyle.Latex => raw"\text{$name}"
      case _ => name
    }
    def prettyParameters(parameters: Seq[String]): String =
      if(parameters.isEmpty) "" else s"${p.s.SquareBracketOpen}${parameters.mkString(p.s.Semicolon + (if(compact) "" else " "))}${p.s.SquareBracketClose}"
    def prettyFormula(f: FOL.Formula): String = FrontPositionedPrinter.prettyFormula(fromKernel(f), style, compact)
    def prettyTerm(t: FOL.Term): String = FrontPositionedPrinter.prettyTerm(fromKernel(t), style, compact)
    def prettyFunction(label: FOL.FunctionLabel, lambda: FOL.LambdaTermTerm): String =
      prettyFormula(FOL.PredicateFormula(FOL.equality, Seq(FOL.FunctionTerm(label, lambda.vars.map(FOL.FunctionTerm(_, Seq.empty))), lambda.body)))
    def prettyPredicate(label: FOL.PredicateLabel, lambda: FOL.LambdaTermFormula): String =
      prettyFormula(FOL.ConnectorFormula(FOL.Iff, Seq(FOL.PredicateFormula(label, lambda.vars.map(FOL.FunctionTerm(_, Seq.empty))), lambda.body)))
    val placeholder = "_"

    def wrap(scProof: lisa.kernel.proof.SCProof): ProofWrapper = {
      val steps = scProof.steps.map { step =>
        val (name: String, parameters: Seq[String]) = step match {
          case s: SC.Hypothesis => (r.Hypothesis, Seq(prettyFormula(s.phi)))
          case s: SC.Cut => (r.Cut, Seq(prettyFormula(s.phi)))
          case _: SC.Rewrite => (r.Rewrite, Seq.empty)
          case _: SC.Weakening => (r.Weakening, Seq.empty)
          case s: SC.LeftAnd => (r.LeftAnd, Seq(s.phi, s.psi).map(prettyFormula))
          case s: SC.RightAnd => (r.RightAnd, s.cunjuncts.map(prettyFormula))
          case s: SC.LeftOr => (r.LeftOr, s.disjuncts.map(prettyFormula))
          case s: SC.RightOr => (r.RightOr, Seq(s.phi, s.psi).map(prettyFormula))
          case s: SC.LeftImplies => (r.LeftImplies, Seq(s.phi, s.psi).map(prettyFormula))
          case s: SC.RightImplies => (r.RightImplies, Seq(s.phi, s.psi).map(prettyFormula))
          case s: SC.LeftIff => (r.LeftIff, Seq(s.phi, s.psi).map(prettyFormula))
          case s: SC.RightIff => (r.RightIff, Seq(s.phi, s.psi).map(prettyFormula))
          case s: SC.LeftNot => (r.LeftNot, Seq(prettyFormula(s.phi)))
          case s: SC.RightNot => (r.RightNot, Seq(prettyFormula(s.phi)))
          case s: SC.LeftForall => (r.LeftForall, Seq(prettyFormula(s.phi), s.x.id, prettyTerm(s.t)))
          case s: SC.RightForall => (r.RightForall, Seq(prettyFormula(s.phi), s.x.id))
          case s: SC.LeftExists => (r.LeftExists, Seq(prettyFormula(s.phi), s.x.id))
          case s: SC.RightExists => (r.RightExists, Seq(prettyFormula(s.phi), s.x.id, prettyTerm(s.t)))
          case s: SC.LeftExistsOne => (r.LeftExistsOne, Seq(prettyFormula(s.phi), s.x.id))
          case s: SC.RightExistsOne => (r.RightExistsOne, Seq(prettyFormula(s.phi), s.x.id))
          case s: SC.LeftRefl => (r.LeftRefl, Seq(prettyFormula(s.fa)))
          case s: SC.RightRefl => (r.RightRefl, Seq(prettyFormula(s.fa)))
          case s: SC.LeftSubstEq => (r.LeftSubstEq, s.equals.flatMap { case (l, r) => Seq(l, r) }.map(prettyTerm)
            :+ prettyPredicate(FOL.ConstantPredicateLabel(placeholder, s.lambdaPhi.vars.size), s.lambdaPhi))
          case s: SC.RightSubstEq => (r.RightSubstEq, s.equals.flatMap { case (l, r) => Seq(l, r) }.map(prettyTerm)
            :+ prettyPredicate(FOL.ConstantPredicateLabel(placeholder, s.lambdaPhi.vars.size), s.lambdaPhi))
          case s: SC.LeftSubstIff => (r.LeftSubstIff, s.equals.flatMap { case (l, r) => Seq(l, r) }.map(prettyFormula)
            :+ prettyPredicate(
              FOL.ConstantPredicateLabel(placeholder, s.lambdaPhi.vars.size),
              FOL.LambdaTermFormula(s.lambdaPhi.vars.map(v => FOL.SchematicFunctionLabel(v.id, v.arity)), s.lambdaPhi.body)
            ))
          case s: SC.RightSubstIff => (r.RightSubstIff, s.equals.flatMap { case (l, r) => Seq(l, r) }.map(prettyFormula)
            :+ prettyPredicate(
            FOL.ConstantPredicateLabel(placeholder, s.lambdaPhi.vars.size),
            FOL.LambdaTermFormula(s.lambdaPhi.vars.map(v => FOL.SchematicFunctionLabel(v.id, v.arity)), s.lambdaPhi.body)
          ))
          case s: SC.InstFunSchema => (r.FunInstantiation, s.insts.toSeq.map { case (label, lambda) => prettyFunction(label, lambda) })
          case s: SC.InstPredSchema => (r.PredInstantiation, s.insts.toSeq.map { case (label, lambda) => prettyPredicate(label, lambda) })
          case SC.SCSubproof(_, _, true) => (r.SubproofShown, Seq.empty)
          case SC.SCSubproof(_, _, false) => (r.SubproofHidden, Seq.empty)
        }
        step match {
          case SC.SCSubproof(sp, premises, true) =>
            SubproofStepWrapper(name, wrap(sp), premises)
          case _ =>
            NormalStepWrapper(name, step.premises, sequentFromKernel(step.bot), if(explicit) parameters else Seq.empty)
        }
      }

      ProofWrapper(steps, scProof.imports.map(sequentFromKernel))
    }

    val proof = wrap(scProof)

    def prettyStepName(step: StepWrapper): String =
      Seq(
        step.name,
        if(style == Latex) "~" else " ",
        step.premises.map(i => if(style == Latex && i < 0) s"{$i}" else i).mkString(", "),
      ).mkString

    val columnInterleaving = style match {
      case Latex => " & "
      case _ => " "
    }

    def computeNumberColumnEnds(proof: ProofWrapper, nextColumnStart: Int, path: Seq[Int]): Map[Seq[Int], Int] = {
      val maxCharCount = Seq(-proof.imports.size, proof.steps.size - 1).map(_.toString.length).max
      val columnEnd = nextColumnStart + maxCharCount - 1
      val newNextColumnStart = columnEnd + 1 + columnInterleaving.length
      proof.steps.zipWithIndex.map {
        case (SubproofStepWrapper(_, subProof, _), i) =>
          computeNumberColumnEnds(subProof, newNextColumnStart, i +: path)
        case _ => Map.empty
      }.fold(Map.empty)(_ ++ _) + (path -> columnEnd)
    }
    val numberColumnEnds = computeNumberColumnEnds(proof, 0, Seq.empty)
    val maximumNumberColumnEnd = numberColumnEnds.values.max
    val maximumNumberColumnDepth = numberColumnEnds.keys.map(_.size).max

    def computeMaximumRuleNameLength(proof: ProofWrapper): Int =
      proof.steps.map {
        case step @ SubproofStepWrapper(_, proof, _) => Math.max(prettyStepName(step).length, computeMaximumRuleNameLength(proof))
        case other => prettyStepName(other).length
      }.max
    val maximumRuleNameLength = computeMaximumRuleNameLength(proof)

    def recursivePrint(proof: ProofWrapper, path: Seq[Int]): Seq[(String, String)] = {
      val importsPairs = proof.imports.zipWithIndex.map { case (s, i) => (-(i + 1), NormalStepWrapper(prettyName("Import"), Seq.empty, s, Seq.empty)) }.reverse
      val stepsTriplets = proof.steps.zipWithIndex.map { case (step, i) =>
        val option = step match {
          case SubproofStepWrapper(_, proof, _) => Some(proof)
          case _ => None
        }
        ((i, step), option)
      }

      def prettyLine(i: Int, step: StepWrapper): String = {
        val numberColumn = i.toString
        val numberColumnEnd = numberColumnEnds(path)
        val nameWithPremises = prettyStepName(step)

        val (leftLength, rightLength) = (numberColumnEnd - numberColumn.length + 1, maximumNumberColumnEnd - numberColumnEnd)
        val (leftSpace, rightSpace) = (columnInterleaving * path.size, columnInterleaving * (maximumNumberColumnDepth - path.size))

        leftSpace + (" " * (leftLength - leftSpace.length)) +
          numberColumn +
          (" " * (rightLength - rightSpace.length)) + rightSpace +
          columnInterleaving +
          nameWithPremises +
          (" " * (maximumRuleNameLength - nameWithPremises.length)) +
          columnInterleaving +
          FrontPositionedPrinter.prettySequent(step.sequent, style, compact)
      }

      importsPairs.map(prettyLine).map(_ -> "") ++ stepsTriplets.flatMap { case ((i, step), option) =>
        (prettyLine(i, step), prettyParameters(step.parameters)) +: option.toSeq.flatMap(proof => recursivePrint(proof, i +: path))
      }
    }

    val lineSeparator = style match {
      case Latex => " \\\\\n"
      case _ => "\n"
    }

    val allLinesPairs = recursivePrint(proof, Seq.empty)
    val maximumLengthFirst = allLinesPairs.map { case (first, _) => first.length }.max
    val content = allLinesPairs.map { case (first, second) =>
      Seq(first, " " * (maximumLengthFirst - first.length), if(explicit) columnInterleaving else "", second).mkString.replaceAll("\\s+$", "")
    }.mkString(lineSeparator)

    style match {
      case FrontPrintStyle.Latex =>
        Seq(
          raw"\tiny",
          raw"$$\begin{array}{${(0 to maximumNumberColumnDepth).map(i => raw"r${if(i < maximumNumberColumnDepth) raw"@{\hskip 0.1cm}" else ""}").mkString}ll${if(explicit) "l" else ""}}",
          content,
          raw"\end{array}$$",
          raw"\normalsize",
        ).mkString("\n")
      case _ => content
    }
  }

}
