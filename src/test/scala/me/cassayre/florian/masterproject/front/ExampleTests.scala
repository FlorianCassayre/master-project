package me.cassayre.florian.masterproject.front

import scala.language.adhocExtensions

import org.scalatest.funsuite.AnyFunSuite
import me.cassayre.florian.masterproject.examples.*

class ExampleTests extends AnyFunSuite {
  test("front interactive proof (1)") {
    frontInteractiveProof1()
  }

  test("front interactive proof (2)") {
    frontInteractiveProof2()
  }

  test("front matching") {
    frontMatching()
  }

  test("front parsing & printing") {
    frontParsingPrinting()
  }

  test("front solver") {
    frontSolver()
  }
}
