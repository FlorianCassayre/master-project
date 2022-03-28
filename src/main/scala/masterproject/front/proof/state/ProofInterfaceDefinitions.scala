package masterproject.front.proof.state

trait ProofInterfaceDefinitions extends ProofEnvironmentDefinitions {

  case class ProofMode private(private var currentState: ProofModeState) {
    def state: ProofState = currentState.state
    def proving: ProofState = currentState.proving
    def apply(tactic: Tactic): Boolean = {
      println()
      print(s"Trying to apply '${tactic.getClass.getSimpleName}'...")
      val result = applyTactic(currentState, tactic) match {
        case Some(newState) =>
          println(" [success]")
          currentState = newState
          true
        case None =>
          println(" [!!! failure !!!]")
          false
      }
      println()
      println(currentState.state)
      result
    }
    def asTheorem()(using env: ProofEnvironment): Theorem = {
      require(state.goals.isEmpty)
      val theorem = env.mkTheorem(Proof(proving.goals: _*)(currentState.tactics: _*))
      println()
      println(theorem)
      println()
      theorem
    }
    override def toString: String =
      (Seq("subgoals:", currentState.state.toString) ++ Seq("proving:", currentState.proving.toString)).mkString("\n")
  }
  object ProofMode {
    def apply(goals: Sequent*)(using environment: ReadableProofEnvironment): ProofMode = {
      val initial = ProofMode(initialProofModeState(goals: _*)(environment))
      println(initial.state)
      initial
    }
  }

}
