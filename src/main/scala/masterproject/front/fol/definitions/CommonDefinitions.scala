package masterproject.front.fol.definitions

trait CommonDefinitions {

  trait Label {
    val id: String
  }
  trait SchematicLabel extends Label

  type Arity = Int & Singleton

  trait WithArity[N <: Arity] {
    val arity: N
  }

}
