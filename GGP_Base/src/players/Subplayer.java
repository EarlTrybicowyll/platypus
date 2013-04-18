package players;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;

public abstract class Subplayer implements Runnable{
	StateMachine stateMachine;
	Role role;
	PlayerResult playerResult;
	MachineState currentState;
	Thread parentThread;
	
	public Subplayer(StateMachine stateMachine, Role role,
			PlayerResult playerResult, MachineState currentState, Thread parentThread) {
		this.stateMachine = stateMachine;
		this.role = role;
		this.playerResult = playerResult;
		this.currentState = currentState;
		this.parentThread = parentThread;
	}
}
