package players;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

import players.GameNode;

public class MonteCarloTreeSearchThread extends Thread{

	private StateMachine stateMachine;
	private Role role;
	private MachineState initialState;
	private long timeout;
	private int numDepthCharges = 0;
	
	private Map<MachineState,GameNode> stateValues = new HashMap<MachineState, GameNode>();


	public MonteCarloTreeSearchThread(StateMachine stateMachine, Role role, MachineState initialState, long timeout){
		this.stateMachine = stateMachine;
		this.role = role;
		this.initialState = initialState;
		this.timeout = timeout;
	}
	
	
	public void run(){
		
		GameNode currentNode = new GameNode(initialState);
		try{
			while(true){
				/* Loop over 4 stages until time is up */
	
				/* Select the next node to expand */
				GameNode targetNode = select(currentNode);
	
				expand(targetNode);
				/* Estimate value of leaf */
				double simulatedValue= 0;
				MachineState simulatedTerminalState = stateMachine.performDepthCharge(targetNode.state, null);
				simulatedValue+= stateMachine.getGoal(simulatedTerminalState, role);
				//System.out.println("Terminal State: " + simulatedTerminalState);
				numDepthCharges++;
				/* Put the values back into the tree! */
				backPropogate(targetNode,simulatedValue);
				if(System.currentTimeMillis()>timeout) break;
			}
			
		} catch (MoveDefinitionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (GoalDefinitionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (TransitionDefinitionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public Map<MachineState, GameNode> getStateValues(){
		return stateValues;
	}
	public int getNumDepthCharges(){
		return numDepthCharges;
	}

	/**
	 * If unexpanded (nodes with more game states to follow, but no children in our tree) nodes exist below the startNode,
	 * selects an unexpanded node and returns it.  If all nodes have been visited, the node returned is selected by 
	 * whichever node has the largest value given by selectFunction
	 * @param startNode the node to start searching the tree from
	 * @return a GameNode to be expanded
	 */

	private GameNode select(GameNode startNode){
		if(startNode.numVisits==0) return startNode;
		/* checks if any children have not yet been expanded; if so, returns them */
		if(startNode.children==null) return startNode;
		for(GameNode gn : startNode.children){

			if(gn.numVisits==0) {
				return gn;
			}
		}
		double bestScore = 0;
		GameNode bestNode = startNode;
		/* Choose the best child node based on a hueristic function selectFunction and then go down that branch looking for
		 * an unexpanded node.
		 */

		//Collections.shuffle(startNode.children); //This might be needed in the future, but it runs the program out of memory if called repeatedly
		for(GameNode gn : startNode.children){
			double newScore = selectFunction(gn);
			if(newScore > bestScore){
				bestScore = newScore;
				bestNode = gn;
			}
		}
		return select(bestNode);
	}

	/**
	 * Returns a heuristic to estimate the simulated value of the given node based on visits and its current value
	 * @param node
	 * @return
	 */

	public double selectFunction(GameNode node){
		return node.value / node.numVisits +100*Math.sqrt(2*Math.log(node.parent.numVisits)/(double)node.numVisits);// + rand.nextDouble()*epsilon;
	}

	/**
	 * Expands the given GameNode to make use of its children, creating new GameNodes for each child and initializing their
	 * values and visits to 0
	 * @param startNode
	 * @throws MoveDefinitionException 
	 * @throws TransitionDefinitionException 
	 * @throws GoalDefinitionException 
	 */

	private void expand(GameNode startNode) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{
		//log.info("failed to expand");
		if(stateMachine.isTerminal(startNode.state)) return;



		startNode.children = new LinkedList<GameNode>();


		Random r = new Random();
		double result = r.nextDouble();
		//if(result<0.05) System.out.println("Starting State: " + startNode.state);
		List<MachineState> nextStates = stateMachine.getNextStates(startNode.state);
		//			if(result<0.05) {
		//				System.out.println("Ending States: " + nextStates);
		//				for(MachineState state : nextStates){
		//					System.out.println(state + " - Terminal - " + stateMachine.isTerminal(state));
		//				}
		//			}
		/* Remove any terminal states where it gets a score of 0 from consideration */
		for(MachineState state: nextStates){
			GameNode newChild = new GameNode(state);
			startNode.children.add(newChild);
			newChild.parent = startNode;
		}
		//log.info("added " + startNode.children.size() + " new nodes ");
	}

	/**
	 * Updates the value of the given node in the game tree as well as the values of all of its parents.  Also updates visited counts.
	 * Updates the value associated in the map to be the average value of the node
	 * @param finalNode
	 * @param value
	 */

	private void backPropogate(GameNode finalNode, double value){
		/* Update value in map */

		finalNode.numVisits++;
		finalNode.value+=value;
		stateValues.put(finalNode.state, finalNode);
		if(finalNode.parent!=null){
			backPropogate(finalNode.parent,value);
		}
	}
}
