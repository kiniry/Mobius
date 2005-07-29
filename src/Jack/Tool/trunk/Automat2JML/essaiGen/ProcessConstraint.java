
/* Generated automatically on Fri Jul 08 17:48:16 CEST 2005*/

package essaiGen ; 


public class ProcessConstraint { 


	//Local variables
	//(None to be added)


	//State Definition
	/*@ public final static ghost int CardIdle = 0 ; @*/ 
	/*@ public final static ghost int Working = 1 ; @*/ 
	/*@ public static int state = CardIdle ; @*/ 

	//nodes invariants
	/*@ static invariant (state==CardIdle || 
	              state==Working ); 
	@*/ 


	/*	Modification function of the Automaton   */
	 /*@ public final static ghost int PROCESSMETHOD_Call = 0; @*/ 
	 /*@ public final static ghost int PROCESSMETHOD_NT = 1; @*/ 
	 /*@ public final static ghost int PROCESSMETHOD_ET = 2; @*/ 


	//@ modifies \nothing ; 
	/*@ ensures ((methodAction==ProcessConstraint.PROCESSMETHOD_Call && ProcessConstraint.state==ProcessConstraint.CardIdle && true) ==> \result==Working) && 
		((methodAction==ProcessConstraint.PROCESSMETHOD_NT && ProcessConstraint.state==ProcessConstraint.Working && !GlobalDefinitionClass.performingTransaction) ==> \result==CardIdle) && 
		((methodAction==ProcessConstraint.PROCESSMETHOD_ET && ProcessConstraint.state==ProcessConstraint.Working && !GlobalDefinitionClass.performingTransaction) ==> \result==CardIdle)  ; @*/ 
	/*@ ensures (!(methodAction==ProcessConstraint.PROCESSMETHOD_Call && ProcessConstraint.state==ProcessConstraint.CardIdle && true) && 
			!(methodAction==ProcessConstraint.PROCESSMETHOD_NT && ProcessConstraint.state==ProcessConstraint.Working && !GlobalDefinitionClass.performingTransaction) && 
			!(methodAction==ProcessConstraint.PROCESSMETHOD_ET && ProcessConstraint.state==ProcessConstraint.Working && !GlobalDefinitionClass.performingTransaction) ) ==> \result==state ; @*/ 
	public static /*@pure@*/ int goNext(int methodAction);

}