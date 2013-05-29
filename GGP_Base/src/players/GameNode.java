package players;

import java.util.List;

import org.ggp.base.util.statemachine.MachineState;

public class GameNode {
	List<GameNode> children = null;
	GameNode parent = null;
	double value = 0;
	int numVisits = 0;
	MachineState state;
	public GameNode(MachineState state){
		this.state = state;
	}
}
