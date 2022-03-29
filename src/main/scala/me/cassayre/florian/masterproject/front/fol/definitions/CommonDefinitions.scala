package me.cassayre.florian.masterproject.front.fol.definitions

trait CommonDefinitions {

  private[fol] trait Label {
    val id: String
  }
  private[fol] trait SchematicLabel extends Label

  private[fol] trait LabeledTree[A <: Label] {
    val label: A
  }

  type Arity = Int & Singleton

  private[fol] trait WithArity[N <: Arity] {
    val arity: N
  }

}
