package players;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.logging.Logger;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

/*** NOT TESTED ***/

public class BryceMonteCarloTreeSearch_NoMiniMax extends Subplayer{


	private Map<MachineState,GameNode> stateValues = new HashMap<MachineState, GameNode>();
	//private Map<MachineState,Integer> stateVisits = new HashMap<MachineState, Integer>();
	//private Map<MachineState,List<MachineState>> stateChildren = new HashMap<MachineState,List<MachineState>>();
	private static Random rand = new Random();
	private static final double epsilon = 1e-6;

	/* Enables a check to only expand to nodes that won't cause the player to get a score of 0 in a terminal state */
	private static final boolean GUARANTEED_LOSSES_SINGLE_MOVE_CHECK = false;

	public BryceMonteCarloTreeSearch_NoMiniMax(StateMachine stateMachine, Role role,
			PlayerResult playerResult, MachineState currentState, Logger logger) {
		super(stateMachine, role, playerResult, currentState, logger);

	}


	@Override
	public void run() {
		try {
			GameNode currentNode = new GameNode(currentState);
			int numDepthCharges = 0;
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
				if(Thread.currentThread().isInterrupted()) break;
			}

			System.out.println("Depth charges: " + numDepthCharges);
			/*  Choose the move that gives the node with the highest value to give back to the player */
			double bestValue = Double.MIN_VALUE;

			Move bestMove = null;
			List<Move> moves = stateMachine.getLegalMoves(currentState, role);
			for(Move move : moves){
				List<List<Move>> jointMoves = stateMachine.getLegalJointMoves(currentState, role, move);
				double moveMinValue = Double.MAX_VALUE;

				/* Playing conservatively, see what the lowest value is that an opponent could cause this move to have */
				int totalVisits = 0;
				for(List<Move> movesToMake : jointMoves){
					MachineState acquiredState = stateMachine.getNextState(currentState,movesToMake);
					GameNode acquiredNode = stateValues.get(acquiredState);
					//System.out.println(acquiredNode);
					if(acquiredNode!=null){
						double acquiredStateValue = acquiredNode.value/acquiredNode.numVisits;
						//System.out.println(movesToMake + "AcquiredStateValue: " + acquiredStateValue);
						if(acquiredStateValue < moveMinValue){
							moveMinValue = acquiredStateValue;
						}
						totalVisits +=acquiredNode.numVisits;
					}else{
						System.out.println("Move not explored in tree: " + movesToMake);
					}
				}
				log.info("move: " + move + " value: " + moveMinValue + " visited: " + totalVisits);
				if(moveMinValue > bestValue){
					bestMove = move;
					bestValue = moveMinValue;
				}
			}

			playerResult.setBestMoveSoFar(bestMove);

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
		if(GUARANTEED_LOSSES_SINGLE_MOVE_CHECK){

			List<Move> legalMoves = stateMachine.getLegalMoves(startNode.state, role);
			//Set<Move> losingMoves = new HashSet<Move>();
			for (Move move : legalMoves) {
				List<List<Move>> jointMoves = stateMachine.getLegalJointMoves(startNode.state, role, move);

				for(List<Move> jointMove : jointMoves){
					Random r = new Random();
					double result = r.nextDouble();
					if(result<0.05) System.out.println("Starting State: " + startNode.state);
					MachineState nextState = stateMachine.getNextState(startNode.state, jointMove);
					
					if (!stateMachine.isTerminal(nextState) || (stateMachine.isTerminal(nextState) && stateMachine.getGoal(nextState,role)!=0)) {
						GameNode newChild = new GameNode(nextState);
						startNode.children.add(newChild);
						newChild.parent = startNode;
					}
				}
			}
			if(startNode.children.size()==0){
				log.warning("Only Guaranteed Losses Found: " + startNode.state);
			}
		} else
		{


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
	
	private class GameNode{
		List<GameNode> children = null;
		GameNode parent = null;
		double value = 0;
		int numVisits = 0;
		MachineState state;
		public GameNode(MachineState state){
			this.state = state;
		}
	}
}






