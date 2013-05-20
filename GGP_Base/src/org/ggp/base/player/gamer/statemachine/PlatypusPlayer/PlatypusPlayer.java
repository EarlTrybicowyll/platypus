package org.ggp.base.player.gamer.statemachine.PlatypusPlayer;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.logging.Logger;

import org.ggp.base.apps.player.detail.DetailPanel;
import org.ggp.base.apps.player.detail.SimpleDetailPanel;
import org.ggp.base.player.gamer.event.GamerSelectedMoveEvent;
import org.ggp.base.player.gamer.exception.GameAnalysisException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.propnet.FirstPropNetStateMachine;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

import platypus.logging.PlatypusLogger;
import platypus.utils.StateSave;
import players.BryceMonteCarloTreeSearch;
import players.PlayerResult;
import players.TerminalStateProximity;
import players.WinCheckBoundedSearch;

public class PlatypusPlayer extends StateMachineGamer {

	private static final String PLAYER_NAME = "Platypus";

	private List<Move> optimalSequence = null;
	private PlayerResult playerResult = new PlayerResult();
	private TerminalStateProximity terminalStateProximity;

	// Optional second argument - level of logging. Default is ALL. Logs to
	// logs/platypus
	private static Logger log = PlatypusLogger.getLogger("game"
			+ System.currentTimeMillis());

	@Override
	public StateMachine getInitialStateMachine() {
		// TODO Auto-generated method stub
		return new FirstPropNetStateMachine();
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {

		terminalStateProximity = new TerminalStateProximity(timeout - 1000,
				getStateMachine(), getCurrentState(), getRole(), log);

		// if(getStateMachine().getRoles().size()==1){
		// /* Single-player game, so try to brute force as much as possible */
		// optimalSequence =
		// solveSinglePlayerGame(getStateMachine(),getCurrentState());
		// }

	}

	public List<Move> solveSinglePlayerGame(StateMachine theMachine,
			MachineState start) throws MoveDefinitionException,
			GoalDefinitionException, TransitionDefinitionException {
		if (theMachine.isTerminal(start)) {
			if (theMachine.getGoal(start, getRole()) == 100) {
				System.out.println("Solved!");
				return new ArrayList<Move>();
			} else {
				/* No optimal state found */
				return null;
			}
		}
		List<Move> moves = theMachine.getLegalMoves(start, getRole());
		List<Move> bestMoves = null;
		for (Move moveUnderConsideration : moves) {
			List<Move> partialBest = solveSinglePlayerGame(theMachine,
					theMachine.getRandomNextState(start, getRole(),
							moveUnderConsideration));
			if (partialBest != null) {
				partialBest.add(moveUnderConsideration);
				bestMoves = partialBest;
				break;
			}
		}
		return bestMoves;
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		long start = System.currentTimeMillis();
		playerResult.setBestMoveSoFar(null);

		//System.out.println("Called select move with:");
		//System.out.println("Current State: " + getCurrentState().toString());
		//System.out.println("Current Role: " + getRole().toString());
		String stateFile = StateSave.save(getCurrentState());
		String roleFile = StateSave.save(getRole());
		//System.out.println("State written to: " + stateFile);
		//System.out.println("Role written to: " + roleFile);
		
		StateMachine machine = getStateMachine();
		if(machine instanceof FirstPropNetStateMachine){
			FirstPropNetStateMachine propMachine = (FirstPropNetStateMachine)machine;
			for(int i = 0; i<propMachine.getNumPropNets(); i++){
				propMachine.setPropNet(i);
				if(propMachine.getLegalMoves(getCurrentState(), getRole()).size()>0){
					System.out.println("PlatypusPlayer:  Found a valid factor.");
					break;
				}
			}
		}

		List<Move> moves = getStateMachine().getLegalMoves(getCurrentState(),
				getRole());
		if (moves.size() == 1) {
			Move bestMove = moves.get(0);
			long stop = System.currentTimeMillis();
			notifyObservers(new GamerSelectedMoveEvent(moves, bestMove, stop
					- start));
			return bestMove;
		}

		// if(getStateMachine().getRoles().size()==1){
		// /* Single-player game */
		// if(optimalSequence!=null){
		// /* Best move is the first move in the sequence */
		// Move bestMove = optimalSequence.remove(optimalSequence.size()-1);
		// long stop = System.currentTimeMillis();
		// notifyObservers(new GamerSelectedMoveEvent(moves, bestMove, stop -
		// start));
		// return bestMove;
		// }
		//
		// }

		// Thread singleSearchPlayer = new Thread(new
		// SingleSearchPlayer(getStateMachine(), getRole(),
		// singleSearchPlayerResult,getCurrentState()));

		// Thread playerThread = new Thread(new
		// MinimaxMonteCarloSubplayer(getStateMachine(), getRole(),
		// playerResult,getCurrentState(), terminalStateProximity,
		// timeout-2000));

		/* Allocate 10% of time to basic minimax */
		// Thread minimaxPlayerThread = new Thread(new MinimaxSubplayer)

		Thread minimaxThread = new Thread(new WinCheckBoundedSearch(
				getStateMachine(), getRole(), playerResult, getCurrentState(),
				log));
		minimaxThread.start();

		try {
			/* Sleep for 2 seconds less than the maximum time allowed */
			Thread.sleep(2500);
		} catch (InterruptedException e) {
			//System.out.println("Done with subplayer!");
			// e.printStackTrace();
		}
		/* Tell the thread searching for the best move it is done so it can exit */
		minimaxThread.interrupt();
		Move sureMove = playerResult.getSureMove();
		log.info("--------Best Move after Minimiax--------");
		if (sureMove == null) {
			log.info("sure move is null: Minimax did not result in anything");
		}else {
			log.info("Sure move is " + playerResult.sureMove);
			log.info("with the sure score of " + playerResult.getSureScore());
			
			if (playerResult.sureScore == 100 || playerResult.getGameSolved()){
				long stop = System.currentTimeMillis();
				log.info("Game solved!");
				log.info("Choosing move "+ playerResult.sureMove + " after minimax preliminary search");
				notifyObservers(new GamerSelectedMoveEvent(moves, sureMove, stop- start));
				return sureMove;
			}
		}
		

		Thread playerThread = new Thread(new BryceMonteCarloTreeSearch(
				getStateMachine(), getRole(), playerResult, getCurrentState(),
				log));
		log.info("Starting Monte Carlo");
		playerThread.start();
		try {
			/* Sleep for 1 secondd less than the maximum time allowed */
			long sleeptime = timeout - System.currentTimeMillis() - 2000 - 1000;
			log.info("PAUSING PLATYPUS FOR " + sleeptime);
			Thread.sleep(sleeptime);
		} catch (InterruptedException e) {
			log.info("Done with subplayer!");
			// e.printStackTrace();
		}
		/* Tell the thread searching for the best move it is done so it can exit */
		playerThread.interrupt();
		try {
			/* Sleep for 2 seconds less than the maximum time allowed */
			Thread.sleep(1000);
		} catch (InterruptedException e) {
			log.info("Done with subplayer!");
			// e.printStackTrace();
		}
		Move bestMove = playerResult.getBestMoveSoFar();
		log.info("--------Best Move after Monte Carlo--------");
		if (bestMove == null) {
			bestMove = moves.get(new Random().nextInt(moves.size()));
			log.info("CHOSE RANDOM");
		}
		long stop = System.currentTimeMillis();
		log.info("best move: " + bestMove);
		notifyObservers(new GamerSelectedMoveEvent(moves, bestMove, stop
				- start));
		//log.info("Time left: " + timeout-)
		return bestMove;
	}

	@Override
	public void stateMachineStop() {
		// TODO Auto-generated method stub

	}

	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub

	}

	@Override
	public void analyze(Game g, long timeout) throws GameAnalysisException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return PLAYER_NAME;
	}

	@Override
	public DetailPanel getDetailPanel() {
		return new SimpleDetailPanel();
	}

}