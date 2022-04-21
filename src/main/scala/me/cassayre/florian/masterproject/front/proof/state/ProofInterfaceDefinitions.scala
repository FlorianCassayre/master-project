package me.cassayre.florian.masterproject.front.proof.state

trait ProofInterfaceDefinitions extends ProofEnvironmentDefinitions {

  private def prettyFrame(string: String, verticalPadding: Int = 0, horizontalPadding: Int = 2): String = {
    val (space, vertical, horizontal, corner) = (' ', '|', '-', '+')
    val lines = string.split("\n")
    val maxLength = lines.map(_.length).max
    val bottomAndTop = (corner +: Seq.fill(maxLength + 2 * horizontalPadding)(horizontal) :+ corner).mkString
    val bottomAndTopMargin = (vertical +: Seq.fill(maxLength + 2 * horizontalPadding)(space) :+ vertical).mkString
    val linesMargin = lines.map(line => Seq(vertical) ++ Seq.fill(horizontalPadding)(space) ++ line.toCharArray ++ Seq.fill(maxLength - line.length + horizontalPadding)(space) ++ Seq(vertical)).map(_.mkString)
    (Seq(bottomAndTop) ++ Seq.fill(verticalPadding)(bottomAndTopMargin) ++ linesMargin ++ Seq.fill(verticalPadding)(bottomAndTopMargin) ++ Seq(bottomAndTop)).mkString("\n")
  }

  case class ProofMode private(private var currentState: ProofModeState) {
    def state: ProofState = currentState.state
    def proving: ProofState = currentState.proving
    def apply(mutator: ProofModeStateMutator): Boolean = {
      print(s"Trying to apply '${mutator.getClass.getSimpleName}'...")
      val result = applyMutator(currentState, mutator) match {
        case Some(newState) =>
          println(" [ok]")
          currentState = newState
          true
        case None =>
          println(" [!!! failure !!!]")
          false
      }
      println()
      println(prettyFrame(currentState.state.toString))
      println()
      result
    }
    def focus(goal: Int): Boolean = apply(TacticFocusGoal(goal))
    def back(): Boolean = apply(CancelPreviousTactic)
    def repeat(tactic: Tactic): Unit = apply(TacticRepeat(tactic))
    def applyOne(tactics: Tactic*): Boolean = apply(TacticFallback(tactics))
    def reset(): Unit = apply(CancelPreviousTactic)
    def asTheorem(): Theorem = {
      require(state.goals.isEmpty, "The proof is incomplete and thus cannot be converted into a theorem")
      val env = currentState.environment
      val theorem = env.mkTheorem(Proof(proving.goals: _*)(currentState.tactics: _*))
      theorem.display()
    }
    override def toString: String =
      (Seq("subgoals:", currentState.state.toString) ++ Seq("proving:", currentState.proving.toString)).mkString("\n")
  }
  object ProofMode {
    def apply(goals: Sequent*)(using environment: ProofEnvironment): ProofMode = {
      val initial = ProofMode(initialProofModeState(goals: _*)(environment))
      println("Entering proof mode")
      println()
      println(prettyFrame(initial.state.toString))
      println()
      initial
    }
  }

  extension [T <: Justified](justified: T) {
    def display(): T = {
      println(justified)
      println()
      justified
    }
  }

}
