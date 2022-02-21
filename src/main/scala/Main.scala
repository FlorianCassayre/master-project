import lisa.kernel.Printer
import lisa.kernel.fol.FOL._
import lisa.KernelHelpers._

object Main extends App {

  val (la, lb) = (ConstantPredicateLabel("a", 0), ConstantPredicateLabel("b", 0))
  val (a, b) = (PredicateFormula(la, Seq.empty), PredicateFormula(lb, Seq.empty))

  println(Printer.prettyFormula((a \/ b) /\ a))

}
