package org.ggp.base.util.statemachine.implementation.propnet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.*;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.propnet.factory.PropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;

import java.util.Collection;


@SuppressWarnings("unused")
public class FirstPropNetStateMachine extends StateMachine {
    /** The underlying proposition network  */
    private PropNet propNet;
    /** The topological ordering of the propositions */
    private List<Proposition> ordering;
    /** The player roles */
    private List<Role> roles;
    
    private List<PropNet> propNets;
    
    /**
     * Initializes the PropNetStateMachine. You should compute the topological
     * ordering here. Additionally you may compute the initial state here, at
     * your discretion.
     */
    @Override
    public synchronized void initialize(List<Gdl> description) {
    	try{
    		propNet = OptimizingPropNetFactory.create(description);
    		roles = propNet.getRoles();
    		ordering = getOrdering();
    		//Set<Set<Component>> factors = factorPropNet();
    		propNets = factorPropNetDumb();
    		
    	}catch(InterruptedException ex){
    		ex.printStackTrace();
    	}
    }    
    
    private boolean propMarkConjunction(Component p, boolean isRecur){
    	for (Component c : p.getInputs()){
			if(!propMarkP(c, isRecur)){
				return false;
			}
		}
		return true;
    }
    
    private boolean propMarkDisjunction(Component p, boolean isRecur){
    	for (Component c : p.getInputs()){
			if(propMarkP(c, isRecur)){
				return true;
			}
		}
		return false;
    }
    
    
  

    
    private boolean propMarkPNonRecursive(Component p){
    	return propMarkP(p, false);
    }
    
    private boolean propMarkPRecursive(Component p){
    	return propMarkP(p, true);
    }
    
    private boolean propMarkP(Component p, boolean isRecur){
    	if(p == null) return false; //for bad legals in mini propnets
    	
    	if(p instanceof Proposition){ //should return false when reaching init?
    		Proposition prop = (Proposition)p;
    		if(isBase(prop) || isInput(prop) || prop == propNet.getInitProposition()){
    			return prop.getValue();
    		}else{
    			if(!isRecur){
    				return p.getValue();
    			}else{
    				if(p.getInputs().size() == 0){
    					return false; // more legals!!!!
    				}
    				return propMarkP(p.getSingleInput(), isRecur);
    			}
    		}
    	}else if (p instanceof Constant){
    		return p.getValue();
    	}else if (p instanceof And){
    		return propMarkConjunction(p, isRecur);
    	}else if (p instanceof Not){
    		return !propMarkP(p.getSingleInput(), isRecur);
    	}else if (p instanceof Or){
    		return propMarkDisjunction(p, isRecur);
    	}
    	return false;
    }
   
    private void clearPropNet(){
    	for(Proposition p : propNet.getPropositions()){
    		p.setValue(false);
    	}
    }
    
    private void markBases(MachineState state){
    	Set<GdlSentence> sentences = state.getContents();
		Map<GdlSentence, Proposition> map = propNet.getBasePropositions();
    	for(GdlSentence s : sentences){
    		Proposition c = map.get(s);
    		if(c!=null){
    			c.setValue(true);
    		}
    	}
    }
	/**
	 * Computes if the state is terminal. Should return the value
	 * of the terminal proposition for the state.
	 */
	@Override
	public synchronized boolean isTerminal(MachineState state) {
		markBases(state);
		boolean result = propMarkPRecursive(propNet.getTerminalProposition());
		clearPropNet();
		//System.out.println("The result: "+result);
		return result;
	}
	
	/* Factors the prop net, but only at the first OR, rather than finding all of the factors */
	private List<PropNet> factorPropNetDumb(){
		List<PropNet> propNets = new ArrayList<PropNet>();
		/* Searching from the terminal component upwards, locate the first OR.  If an AND is found first, the game is deemed
		 * unfactorable.
		 */
		Component bottomOr;
		Component goalProposition = findWinningGoalNode();;
		bottomOr =  findBottomOr(goalProposition);
		
		if(bottomOr!=null){
			/* For each branch leading out of the bottom OR, create a set of all components on which the OR depends,
			 * i.e. find all components in that branch.
			 */
			Set<Set<Component>> factors = new HashSet<Set<Component>>();
			for(Component comp : bottomOr.getInputs()){
				Set<Component> newFactor = new HashSet<Component>();
				getTreeFromBottomComponent(comp,newFactor);
				factors.add(newFactor);
			}
			
			/* Check to see if any of these branches contain the same component.  If any do, naively rule the game as 
			 * unfactorable (it may still be factorable, but not under our simple definition).
			 */
			Set<Component> allDistinctComponents = new HashSet<Component>();
			int totalIndependentSetSize = 0;
			for(Set<Component> factor : factors){
				allDistinctComponents.addAll(factor);
				totalIndependentSetSize+=factor.size();
			}
			
			if(allDistinctComponents.size()<totalIndependentSetSize){
				System.out.println("Found factors, but they weren't independent.");
				propNets.add(propNet);
			} else {
				
			/* Add the bottom of the propnet (bottom OR and below) to each branch*/
				for(Component parent : bottomOr.getInputs()){
					for(Set<Component> factor : factors){
						if(factor.contains(parent)){
							addBottomPropNet(factor,parent, goalProposition);
							
							factor.addAll(propNet.getLegalPropositions().get(roles.get(0)));
						}		
					}
				}
				
			/* Convert sets of components to propnets */
				for(Set<Component> factor : factors){
					propNets.add(new PropNet(roles,factor));
				}
				
				System.out.println("Successfully created " + propNets.size() + " factors.");				
			}
		}else{
			
			/* Only factor is the entire game, so add it */
			propNets.add(propNet);
			System.out.println("Found And instead of Or, so unfactorable.");
		}
		
		return propNets;
	}
	
	

	/**
	 * Explores tree until it finds AND or OR component, returning the component if an Or is found, null otherwise
	 * @param terminalComp place to start in propnet
	 * @return null if and was found, an Or component otherwise
	 */
	private Component findBottomOr(Component terminalComp){
		Component currentComp = terminalComp;
		while(true){
			if(currentComp instanceof Or){
				return currentComp;
			} else if(currentComp instanceof And){
				return null;
			}
			currentComp = currentComp.getSingleInput();
		}
	}
	
	/**
	 * Adds all components on which the given starting component is dependent to a set of components
	 * @param currentComponent
	 * @param components set to contain all components when this function is complete
	 */
	private void getTreeFromBottomComponent(Component currentComponent, Set<Component> components){
		components.add(currentComponent);
		if(isBase(currentComponent) || isInput(currentComponent) || currentComponent == propNet.getInitProposition()){
			return;
		}
		//System.out.println(startComponent);
		for(Component parent : currentComponent.getInputs()){
			getTreeFromBottomComponent(parent, components);
		}
	}
	/**
	 * In the given component, replace the final Or with a new dummy transition that maintains all the outputs of the old or
	 * and adds a new terminal proposition for that component.
	 * @param startComponent the bottom or's parent in this factor
	 */
	private void addBottomPropNet(Set<Component> factor, Component startComponent, Component goal){
		Component dummyTransition = new Or();
		dummyTransition.addInput(startComponent);
		dummyTransition.addOutput(goal);
		Component newTerminalProposition = new Proposition(propNet.getTerminalProposition().getName());
		dummyTransition.addOutput(newTerminalProposition);
		
		startComponent.addOutput(dummyTransition);
		
		
		factor.add(dummyTransition);
		factor.add(newTerminalProposition);
		factor.add(goal);
		
//		Component currentComponent = startComponent;
//		
//		while(true){
//			factor.add(currentComponent);
//			if(currentComponent==propNet.getTerminalProposition()) return;
//			currentComponent = currentComponent.getSingleOutput();
//		}
	}
	
	/* Currently assumes single player */
	private Proposition findWinningGoalNode(){
		Set<Proposition> goalNodes = propNet.getGoalPropositions().get(getRoles().get(0));
		for(Proposition prop : goalNodes){
			if(getGoalValue(prop)==100){
				return prop;
			}
		}
		return null;
	}
	
	
	public void setPropNet(int index){
		propNet = propNets.get(index);
	}
	
	public int getNumPropNets(){
		return propNets.size();
	}
	
	
	
	private Set<Set<Component>> factorPropNet(){
        Map<Component,Set<Component>> propFactors = new HashMap<Component,Set<Component>>();
        
        Set<Component> initialFactor = new HashSet<Component>();
        
        /* Recursively construct factor trees, copying factors at every or transition and joining factors at every and transition 
         * Initialize the starting component to be the terminal node in the net and put it in the initial factor
         */
        Component terminalProp = propNet.getTerminalProposition();
        initialFactor.add(terminalProp);
        propFactors.put(terminalProp,initialFactor);
        
        recursiveFactorPropNet(propFactors,terminalProp);
        
        /* Iterate over base propositions to find distinct complete trees to create set of factors */
        Set<Set<Component>> factors = new HashSet<Set<Component>>(propFactors.values());
        /*Just get the base components factors */
        Set<Set<Component>> baseFactors = new HashSet<Set<Component>>();
        for(Component comp : getBasePropositions()){
        	baseFactors.add(propFactors.get(comp));
        }
        System.out.println("Found " + baseFactors.size() + " base factors.");
        System.out.println("Found " + factors.size() + " factors.");
        return baseFactors;
    }
    
    private void recursiveFactorPropNet(Map<Component,Set<Component>> propFactors, Component currentComponent){
    	if(isBase(currentComponent) || isInput(currentComponent) || currentComponent == propNet.getInitProposition()){
            /* Done with the current factor */
            return;
        }
        
        if(currentComponent instanceof Or){
            /* Create a copy of the factor for each parent, then recurse on those factors */
            for(Component comp : currentComponent.getInputs()){
                Set<Component> newFactor = new HashSet<Component>(propFactors.get(currentComponent));
                newFactor.add(comp);
                propFactors.put(comp,newFactor);
                recursiveFactorPropNet(propFactors, comp);
            }
            return;
        }
        
        if(currentComponent instanceof And){
            /* Merge each of the factors from the parents of the currentComponent, if they exist
             * Add the currentComponent to the factor as well
             */

            Set<Component> mergedSet = propFactors.get(currentComponent);
            
            for(Component comp : currentComponent.getInputs()){
                if(propFactors.containsKey(comp)){
                    Set<Component> parentFactor = propFactors.get(comp);
                    mergedSet.addAll(parentFactor);
                }
                mergedSet.add(comp);
                /* Associate each parent with the new merged set */
                propFactors.put(comp,mergedSet);

            }
            
            for(Component comp : currentComponent.getInputs()){
                /* Recurse on all inputs */
                recursiveFactorPropNet(propFactors,comp);
            }          
            return;
        }
        
        /* Default case, where there is only a single parent.  Simply pass the currentFactor up and add 
         * the current node to that factor.
         */
        Set<Component> currentFactor = propFactors.get(currentComponent);
        Component parent = currentComponent.getSingleInput();
        currentFactor.add(parent);
        propFactors.put(parent, currentFactor);
        
        recursiveFactorPropNet(propFactors,parent);
    }
	
   
	/**
	 * Computes the goal for a role in the current state.
	 * Should return the value of the goal proposition that
	 * is true for that role. If there is not exactly one goal
	 * proposition true for that role, then you should throw a
	 * GoalDefinitionException because the goal is ill-defined. 
	 */
	@Override
	public synchronized int getGoal(MachineState state, Role role)
	throws GoalDefinitionException {
		markBases(state);
		Set<Proposition> goalProps = propNet.getGoalPropositions().get(role);
		boolean found = false;
		Proposition goal = null;
		for(Proposition p : goalProps){
			if(propMarkPRecursive(p)){
				if(found) {
					clearPropNet();
					throw new GoalDefinitionException(state, role);
				}
				found = true;
				goal = p;
			}
		}
		if(!found) {
			clearPropNet();
			throw new GoalDefinitionException(state, role);
		}
		int val = getGoalValue(goal);
		//System.out.println("Goal value: "+val);
		clearPropNet();
		return val;
	}
	
	/**
	 * Returns the initial state. The initial state can be computed
	 * by only setting the truth value of the INIT proposition to true,
	 * and then computing the resulting state.
	 */
	@Override
	public synchronized MachineState getInitialState() {
		propNet.getInitProposition().setValue(true);
		for(Proposition p: ordering){
			p.setValue(propMarkPNonRecursive(p.getSingleInput()));
		}
		MachineState state = getStateFromBase();
		clearPropNet();
		return state;
	}
	
	/**
	 * Computes the legal moves for role in state.
	 */
	@Override
	public synchronized List<Move> getLegalMoves(MachineState state, Role role)
	throws MoveDefinitionException {
		
		//.out.println("Getting Legals for "+state.toString()+" and Role: "+role.toString());
		List<Move> listMoves = new LinkedList<Move>();
		markBases(state);
		Set<Proposition> legals = propNet.getLegalPropositions().get(role);
		for(Proposition legal: legals){
			if(propMarkPRecursive(legal)){
				listMoves.add(getMoveFromProposition(legal));
			}
		}
		//System.out.println("Legals: "+listMoves.size());
		clearPropNet();
		return listMoves;
	}
	
	
	/**
	 * Computes the next state given state and the list of moves.
	 */
	@Override
	public synchronized MachineState getNextState(MachineState state, List<Move> moves)
	throws TransitionDefinitionException {
		//(moves.toString() + " "+state.toString());
		if(moves == null) return state; //not sure exactly what this should be
		
		List<GdlSentence> sentences = toDoes(moves);
		
		markActions(sentences);
		markBases(state);
		
		//HashMap<Proposition, Boolean> next = new HashMap<Proposition, Boolean>();

		for(Proposition p: ordering){
			p.setValue(propMarkPNonRecursive(p.getSingleInput()));
		}
		//for(Proposition p: next.keySet()){
		//	p.setValue(next.get(p));
		//}
		MachineState nextState = getStateFromBase();
		//if(nextState)
		//System.out.println("Next State Contents:"+nextState.getContents().toString());
		clearPropNet();
		return nextState;
	}
	
	private void markActions(List<GdlSentence> sentences){
		Map<GdlSentence, Proposition> inputs = propNet.getInputPropositions();
		for(GdlSentence sentence: sentences){
			Proposition c = inputs.get(sentence);
			if(c!=null) c.setValue(true);
		}
	}
	
	Set<Component> basePropositions = null;
	
	private boolean isBase(Component base){
		
		if(basePropositions!=null){
			return basePropositions.contains(base);
		}
		basePropositions = new HashSet<Component>(propNet.getBasePropositions().values());
		return basePropositions.contains(base);
	}
	
	private Set<Component> getBasePropositions(){
		if(basePropositions!=null){
			return basePropositions;
		}
		basePropositions = new HashSet<Component>(propNet.getBasePropositions().values());
		return basePropositions;
	}
	
	Set<Component> inputPropositions = null;
	
	private boolean isInput(Component base){
		
		if(inputPropositions!=null){
			return inputPropositions.contains(base);
		}
		inputPropositions = new HashSet<Component>();
		for(Component s: propNet.getInputPropositions().values()){
			inputPropositions.add(s);
		}
		return inputPropositions.contains(base);
	}
	
	
	private List<Component> leaves = null;
	private List<Component> getLeaves(){
		if(leaves!=null){
			return leaves;
		}
		leaves = new LinkedList<Component>();
		leaves.addAll(propNet.getBasePropositions().values());
		for(Component c: propNet.getComponents()){
			if(c.getInputs().size() == 0){
				leaves.add(c);
			}
		}
		return leaves;
	}
	
	private boolean seenLink(List<Link>seenLinks, Component src, Component dst){
		for(Link link : seenLinks){
			if(link.dest == dst && link.source == src){
				return true;
			}
		}
		return false;
	}
	private boolean allInputsSeen(Component comp, List<Link> seenLinks){
		Set<Component> inputs = comp.getInputs();
		for(Component input: inputs){
			boolean found = false;
			if(!seenLink(seenLinks, input, comp)){
				return false;
			}
		}
		return true;
	}
	
	private class Link{
		Component source;
		Component dest;
		
		public Link(Component source, Component dest){
			this.source = source;
			this.dest = dest;
		}
		
	}
	/**
	 * This should compute the topological ordering of propositions.
	 * Each component is either a proposition, logical gate, or transition.
	 * Logical gates and transitions only have propositions as inputs.
	 * 
	 * The base propositions and input propositions should always be exempt
	 * from this ordering.
	 * 
	 * The base propositions values are set from the MachineState that
	 * operations are performed on and the input propositions are set from
	 * the Moves that operations are performed on as well (if any).
	 * 
	 * @return The order in which the truth values of propositions need to be set.
	 */
	public synchronized List<Proposition> getOrdering()
	{
	    // List to contain the topological ordering.
	    List<Proposition> order = new LinkedList<Proposition>();
	    				
		// All of the components in the PropNet
		List<Component> components = new ArrayList<Component>(propNet.getComponents());
		
		// All of the propositions in the PropNet.		
		List<Component> noIncoming = getLeaves();
		List<Link> seenLinks = new LinkedList<Link>();
		
		while(noIncoming.size() > 0){
			Component node = noIncoming.remove(0);
			if(node instanceof Proposition && !isBase(node) && !isInput(node) && node != propNet.getInitProposition()){
					order.add((Proposition)node);
			}
			Set<Component> outputs = node.getOutputs();
			for(Component comp : outputs){
				if(seenLink(seenLinks, node, comp)){
					continue;
				}
				//mark the link
				Link link = new Link(node, comp);
				seenLinks.add(link);
				
				if(allInputsSeen(comp, seenLinks)){
					noIncoming.add(comp);
				}
			}
			
		}
		return order;
		
	}
	
	/* Already implemented for you */
	@Override
	public synchronized List<Role> getRoles() {
		return roles;
	}

	/* Helper methods */
		
	/**
	 * The Input propositions are indexed by (does ?player ?action).
	 * 
	 * This translates a list of Moves (backed by a sentence that is simply ?action)
	 * into GdlSentences that can be used to get Propositions from inputPropositions.
	 * and accordingly set their values etc.  This is a naive implementation when coupled with 
	 * setting input values, feel free to change this for a more efficient implementation.
	 * 
	 * @param moves
	 * @return
	 */
	private List<GdlSentence> toDoes(List<Move> moves)
	{
		List<GdlSentence> doeses = new ArrayList<GdlSentence>(moves.size());
		Map<Role, Integer> roleIndices = getRoleIndices();
		
		for (int i = 0; i < roles.size(); i++)
		{
			int index = roleIndices.get(roles.get(i));
			doeses.add(ProverQueryBuilder.toDoes(roles.get(i), moves.get(index)));
		}
		return doeses;
	}
	
	/**
	 * Takes in a Legal Proposition and returns the appropriate corresponding Move
	 * @param p
	 * @return a PropNetMove
	 */
	public synchronized static Move getMoveFromProposition(Proposition p)
	{
		return new Move(p.getName().get(1));
	}
	
	/**
	 * Helper method for parsing the value of a goal proposition
	 * @param goalProposition
	 * @return the integer value of the goal proposition
	 */	
    private int getGoalValue(Proposition goalProposition)
	{
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
	}
	
	/**
	 * A Naive implementation that computes a PropNetMachineState
	 * from the true BasePropositions.  This is correct but slower than more advanced implementations
	 * You need not use this method!
	 * @return PropNetMachineState
	 */	
	public synchronized MachineState getStateFromBase()
	{
		Set<GdlSentence> contents = new HashSet<GdlSentence>();
		for (Proposition p : propNet.getBasePropositions().values())
		{
			p.setValue(p.getSingleInput().getValue());
			if (p.getValue())
			{
				contents.add(p.getName());
			}

		}
		return new MachineState(contents);
	}
}