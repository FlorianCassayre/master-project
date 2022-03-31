package me.cassayre.florian.masterproject.front.fol.ops

import me.cassayre.florian.masterproject.front.fol.definitions.FormulaDefinitions

trait FormulaOps extends CommonOps {
  this: FormulaDefinitions =>

  extension[N <: Arity] (label: PredicateLabel[N])
    def apply: FillArgs[Term, N] => PredicateFormula = args => PredicateFormula(label, tuple2seq(args))
  extension (label: PredicateLabel[0])
    def apply(): PredicateFormula = PredicateFormula(label, Seq.empty)

  extension[N <: Arity] (label: ConnectorLabel[N])
    def apply: FillArgs[Formula, N] => ConnectorFormula = args => ConnectorFormula(label, tuple2seq(args))
  extension (label: ConnectorLabel[0])
    def apply(): ConnectorFormula = ConnectorFormula(label, Seq.empty)

  extension[N <: Arity] (label: BinderLabel)
    def apply(bound: VariableLabel, inner: Formula): BinderFormula = BinderFormula(label, bound, inner)

  given Conversion[PredicateLabel[0], PredicateFormula] = PredicateFormula(_, Seq.empty)
  given Conversion[ConnectorLabel[0], ConnectorFormula] = ConnectorFormula(_, Seq.empty) // For completeness

  given Conversion[Formula, FormulaLabel] = _.label

  extension (f: Formula) {
    def unary_! : ConnectorFormula = ConnectorFormula(neg, Seq(f))
    infix def ==>(g: Formula): ConnectorFormula = ConnectorFormula(implies, Seq(f, g))
    infix def <=>(g: Formula): ConnectorFormula = ConnectorFormula(iff, Seq(f, g))
    infix def /\(g: Formula): ConnectorFormula = ConnectorFormula(and, Seq(f, g))
    infix def \/(g: Formula): ConnectorFormula = ConnectorFormula(or, Seq(f, g))
  }

  extension (t: Term) {
    infix def ===(u: Term): PredicateFormula = PredicateFormula(equality, Seq(t, u))
  }

  // Extractors

  object ! {
    def unapply(f: Formula): Option[Formula] = f match {
      case ConnectorFormula(`neg`, Seq(g)) => Some(g)
      case _ => None
    }
  }

  sealed abstract class UnapplyBinaryConnector(label: ConnectorLabel[2]) {
    def unapply(f: Formula): Option[(Formula, Formula)] = f match {
      case ConnectorFormula(`label`, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }

  object ==> extends UnapplyBinaryConnector(implies)
  object <=> extends UnapplyBinaryConnector(iff)
  object /\ extends UnapplyBinaryConnector(and)
  object \/ extends UnapplyBinaryConnector(or)

  sealed abstract class UnapplyBinaryPredicate(label: PredicateLabel[2]) {
    def unapply(f: Formula): Option[(Term, Term)] = f match {
      case PredicateFormula(`label`, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }

  object === extends UnapplyBinaryPredicate(equality)

}
