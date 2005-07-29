
/* Generated automatically on Fri Jul 08 17:48:16 CEST 2005*/

package essaiGen ; 


public class NoNewObject { 


	//Local variables
	//(None to be added)


	//State Definition
	/*@ public final static ghost int Error = 0 ; @*/ 
	/*@ public final static ghost int Init = 1 ; @*/ 
	/*@ public static int state = Init ; @*/ 

	//nodes invariants
	/*@ static invariant (state==Error || 
	              state==Init ); 
	@*/ 
	//@ static invariant (state==Error) ==> (false) ; 


	/*	Modification function of the Automaton   */
	 /*@ public final static ghost int CONSTRUCTORMETHOD_Call = 0; @*/ 
	 /*@ public final static ghost int CONSTRUCTORMETHOD_NT = 1; @*/ 
	 /*@ public final static ghost int CONSTRUCTORMETHOD_ET = 2; @*/ 


	//@ modifies \nothing ; 
	/*@ ensures ((methodAction==NoNewObject.CONSTRUCTORMETHOD_Call && NoNewObject.state==NoNewObject.Init && GlobalDefinitionClass.performingTransaction) ==> \result==Error)  ; @*/ 
	/*@ ensures (!(methodAction==NoNewObject.CONSTRUCTORMETHOD_Call && NoNewObject.state==NoNewObject.Init && GlobalDefinitionClass.performingTransaction) ) ==> \result==state ; @*/ 
	public static /*@pure@*/ int goNext(int methodAction);

}