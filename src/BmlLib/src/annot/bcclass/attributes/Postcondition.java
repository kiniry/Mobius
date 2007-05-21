package annot.bcclass.attributes;

import annot.bcclass.BMLConfig;
import annot.formula.Formula;
import annot.formula.Predicate0Ar;

//import java.util.Enumeration;
//import java.util.Vector;
//
//import annot.formula.Connector;
//import annot.formula.Formula;
//import bytecode_wp.vcg.VCGPath;

public class Postcondition {
	
	private Formula postcondition;
	
	private SpecificationCase specCase;
	
	public Postcondition(Formula f) {
		postcondition = f;
	}
	
	public String printCode(BMLConfig conf) {
		return postcondition.printLine(conf, 20);
	}
	
	protected void setSpecificationCase(SpecificationCase _specCase) {
		specCase = _specCase;
	}
	
//	/**
//	 * 
//	 * @return the predicate that is assumed to hold after the method is called 
//	 */
//	public  Formula getPostconditionOnMethodCall() {
//		Formula postSpecCase = (Formula) getPostcondition().copy();		
//		//postSpecCase = (Formula)postSpecCase.localVarAtPreState();
//		
//		MethodSpecification mSpec = specCase.getMethodSpecification();
//		
//		/*Formula invariant = (mSpec.getInvariant() == null)?Predicate0Ar.TRUE:(Formula)mSpec.getInvariant().copy();
//		postSpecCase = Formula.getFormula( postSpecCase,  (Formula)invariant.copy(), Connector.AND);*/
//		
//		Formula historyConstraint = (Formula)mSpec.getHistoryConstraint();
//		if (historyConstraint != null) {
//			postSpecCase = Formula.getFormula( postSpecCase , (Formula)historyConstraint.copy(), Connector.AND);
//		}
//		Formula retConstraints =  mSpec.getReturnBoolConstraints();
//		if (retConstraints != null) {
//			postSpecCase = Formula.getFormula( postSpecCase , (Formula)retConstraints.copy(), Connector.AND);
//		}
//			
//		Formula preconditionCase  = specCase.getPrecondition();
//		preconditionCase = (Formula)preconditionCase.copy();
//		preconditionCase = (Formula)preconditionCase.valuesInPreState();
//		postSpecCase = Formula.getFormula(preconditionCase, postSpecCase, Connector.IMPLIES);
//		return postSpecCase;
//	}
//	
//	
//	
//	/**
//	 * generate and return the predicate that must hold in the post state 
//	 * of the method. The second parameter determines the type of 
//	 * the postcondition - either it is a normal termination, or it is an 
//	 * exceptional termination predicate
//	 * @param vcg TODO
//	 * @return
//	 */
//	public void getPostconditionToProve(VCGPath vcg, byte postType) {
//		Formula postSpecCase = (Formula) getPostcondition().copy();
//		
//		postSpecCase = (Formula)postSpecCase.localVarAtPreState();
//		Vector subGoals = postSpecCase.elimConj();
//		Enumeration en = subGoals.elements();
//		
//		while(en.hasMoreElements() ) {
//			Formula f = (Formula) en.nextElement();
//			vcg.addGoal(postType, f );
//			
//		}
//
//		Formula preconditionCase  = specCase.getPrecondition();
//		preconditionCase = (Formula)preconditionCase.copy();
//		// substitute field accesses and local variables with their 
//		// values in the poststate
//		preconditionCase = (Formula)preconditionCase.valuesInPreState();
//		Integer key = vcg.addHyp( 0, preconditionCase);
//		vcg.addHypsToVCs( key);
//		
//		//postSpecCase = Formula.getFormula(preconditionCase, postSpecCase, Connector.IMPLIES);
//		/*return postSpecCase;*/
//	}
//	
//	
//
//	/**
//	 * generate and return the predicate that must hold in the post state 
//	 * of the method when it is called. The second parameter determines the type of 
//	 * the postcondition - either it is a normal termination, or it is an 
//	 * exceptional termination predicate
//	 * @param vcg TODO
//	 * @return
//	 *//*
//	public Formula getPostconditionToAssume( byte postType) {
//		Formula postSpecCase = (Formula) getPostcondition().copy();
//		
//		postSpecCase = (Formula)postSpecCase.localVarAtPreState();
//	
//		Formula preconditionCase  = specCase.getPrecondition();
//		preconditionCase = (Formula)preconditionCase.copy();
//		// substitute field accesses and local variables with their 
//		// values in the poststate
//		preconditionCase = (Formula)preconditionCase.valuesInPreState();
//		postSpecCase = Formula.getFormula( preconditionCase, postSpecCase, Connector.IMPLIES);
//		
//		return postSpecCase;
//		
//		
//	}*/
//	
	/**
	 * @return Returns the postcondition.
	 */
	public Formula getPostcondition() {
		return postcondition;
	}
}
