package me.cassayre.florian.masterproject.front.printer

import lisa.kernel.proof.SequentCalculus as SC
import me.cassayre.florian.masterproject.front.*
import me.cassayre.florian.masterproject.front.printer.FrontPrintStyle.{Ascii, Latex, Unicode}

object KernelPrinter {

  private case class ProofWrapper(steps: IndexedSeq[StepWrapper], imports: IndexedSeq[Sequent])
  private sealed abstract class StepWrapper {
    val name: String
    val sequent: Sequent
    val premises: Seq[Int]
  }
  private case class NormalStepWrapper(name: String, premises: Seq[Int], sequent: Sequent) extends StepWrapper
  private case class SubproofStepWrapper(name: String, proof: ProofWrapper, premises: Seq[Int]) extends StepWrapper {
    override val sequent: Sequent = proof.steps.last.sequent
  }

  def prettyProof(scProof: lisa.kernel.proof.SCProof, style: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false): String = {
    val p = FrontPrintParameters(style, compact)
    def sequentFromKernel(s: lisa.kernel.proof.SequentCalculus.Sequent): Sequent = {
      def sorted(seq: IndexedSeq[Formula]): IndexedSeq[Formula] = seq.sortBy(_.toString)
      Sequent(sorted(s.left.toIndexedSeq.map(fromKernel)), sorted(s.right.toIndexedSeq.map(fromKernel)))
    }
    def prettyName(name: String): String = style match {
      case FrontPrintStyle.Latex => raw"\text{$name}"
      case _ => name
    }
    def wrap(scProof: lisa.kernel.proof.SCProof): ProofWrapper = {
      val steps = scProof.steps.map { step =>
        val nameParts = step match {
          case _: SC.Rewrite => Left("Rewrite")
          case _: SC.Hypothesis => Left("Hypo.")
          case _: SC.Cut => Left("Cut")
          case _: SC.LeftAnd => Right(("Left", p.s.And))
          case _: SC.LeftNot => Right(("Left", p.s.Exclamation))
          case _: SC.RightOr => Right(("Right",p.s.Or))
          case _: SC.RightNot => Right(("Right", p.s.Exclamation))
          case _: SC.LeftExists => Right(("Left", p.s.Exists))
          case _: SC.LeftForall => Right(("Left", p.s.Forall))
          case _: SC.LeftExistsOne => Right(("Left", p.s.ExistsOne))
          case _: SC.LeftOr => Right(("Left", p.s.Or))
          case _: SC.RightExists => Right(("Right", p.s.Exists))
          case _: SC.RightForall => Right(("Right", p.s.Forall))
          case _: SC.RightExistsOne => Right(("Right", p.s.ExistsOne))
          case _: SC.RightAnd => Right(("Right", p.s.And))
          case _: SC.RightIff => Right(("Right", p.s.Iff))
          case _: SC.RightImplies => Right(("Right", p.s.Implies))
          case _: SC.Weakening => Left("Weakening")
          case _: SC.LeftImplies => Right(("Left", p.s.Implies))
          case _: SC.LeftIff => Right(("Left", p.s.Iff))
          case _: SC.LeftRefl => Left("L. Refl")
          case _: SC.RightRefl => Left("R. Refl")
          case _: SC.LeftSubstEq => Left("L. SubstEq")
          case _: SC.RightSubstEq => Left("R. SubstEq")
          case _: SC.LeftSubstIff => Left("L. SubstIff")
          case _: SC.RightSubstIff => Left("R. SubstIff")
          case _: SC.InstFunSchema => Left("?Fun Instantiation")
          case _: SC.InstPredSchema => Left("?Pred Instantiation")
          case SC.SCSubproof(_, _, true) => Left("Subproof")
          case SC.SCSubproof(_, _, false) => Left("Subproof (hidden)")
        }
        val name = nameParts match {
          case Left(value) => prettyName(value)
          case Right((value, symbol)) => s"${prettyName(value)}${if(style == Latex) "~" else " "}$symbol"
        }
        step match {
          case SC.SCSubproof(sp, premises, true) =>
            SubproofStepWrapper(name, wrap(sp), premises)
          case _ =>
            NormalStepWrapper(name, step.premises, sequentFromKernel(step.bot))
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

    def recursivePrint(proof: ProofWrapper, path: Seq[Int]): Seq[String] = {
      val importsPairs = proof.imports.zipWithIndex.map { case (s, i) => (-(i + 1), NormalStepWrapper(prettyName("Import"), Seq.empty, s)) }.reverse
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

      importsPairs.map(prettyLine) ++ stepsTriplets.flatMap { case ((i, step), option) =>
        prettyLine(i, step) +: option.toSeq.flatMap(proof => recursivePrint(proof, i +: path))
      }
    }

    val lineSeparator = style match {
      case Latex => " \\\\\n"
      case _ => "\n"
    }

    val content = recursivePrint(proof, Seq.empty).mkString(lineSeparator)

    style match {
      case FrontPrintStyle.Latex =>
        Seq(
          raw"\tiny",
          raw"$$\begin{array}{${(0 to maximumNumberColumnDepth).map(i => raw"r${if(i < maximumNumberColumnDepth) raw"@{\hskip 0.1cm}" else ""}").mkString}ll}",
          content,
          raw"\end{array}$$",
          raw"\normalsize",
        ).mkString("\n")
      case _ => content
    }
  }

}
