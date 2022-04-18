package me.cassayre.florian.masterproject.test.front

import me.cassayre.florian.masterproject.front.*

@main def tests6(): Unit = {
  val set: Set[SchematicFunctionLabel[?]] = Set(SchematicFunctionLabel[2]("f"))
  set.head match {
    case ll : SchematicFunctionLabel[2] =>
      val ttt: SchematicFunctionLabel[2] = ll
      //val ab: SchematicFunctionLabel[1] = aa
      //println(xx)
  }
}
