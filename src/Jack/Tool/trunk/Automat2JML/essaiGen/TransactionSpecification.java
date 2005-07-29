
/* Generated automatically on Fri Jul 08 17:48:16 CEST 2005*/

package essaiGen ; 


public class TransactionSpecification { 


	//Local variables
	//(None to be added)


	//State Definition
	/*@ public final static ghost int NoTransaction = 0 ; @*/ 
	/*@ public final static ghost int TransactionOpened = 1 ; @*/ 
	/*@ public final static ghost int id10 = 2 ; @*/ 
	/*@ public final static ghost int id7 = 3 ; @*/ 
	/*@ public final static ghost int id9 = 4 ; @*/ 
	/*@ public static int state = NoTransaction ; @*/ 

	//nodes invariants
	/*@ static invariant (state==NoTransaction || 
	              state==TransactionOpened || 
	              state==id10 || 
	              state==id7 || 
	              state==id9 ); 
	@*/ 
	//@ static invariant (state==NoTransaction) ==> (getTransactionDepth()==0) ; 
	//@ static invariant (state==TransactionOpened) ==> (getTransactionDepth()==1) ; 


	/*	Modification function of the Automaton   */
	 /*@ public final static ghost int ABORTTRANSACTION_Call = 0; @*/ 
	 /*@ public final static ghost int ABORTTRANSACTION_NT = 1; @*/ 
	 /*@ public final static ghost int ABORTTRANSACTION_ET = 2; @*/ 
	 /*@ public final static ghost int BEGINTRANSACTION_Call = 3; @*/ 
	 /*@ public final static ghost int BEGINTRANSACTION_NT = 4; @*/ 
	 /*@ public final static ghost int BEGINTRANSACTION_ET = 5; @*/ 
	 /*@ public final static ghost int COMMITTRANSACTION_Call = 6; @*/ 
	 /*@ public final static ghost int COMMITTRANSACTION_NT = 7; @*/ 
	 /*@ public final static ghost int COMMITTRANSACTION_ET = 8; @*/ 


	//@ modifies \nothing ; 
	/*@ ensures ((methodAction==TransactionSpecification.BEGINTRANSACTION_Call && TransactionSpecification.state==TransactionSpecification.NoTransaction && true) ==> \result==id7) && 
		((methodAction==TransactionSpecification.ABORTTRANSACTION_Call && TransactionSpecification.state==TransactionSpecification.TransactionOpened && true) ==> \result==id10) && 
		((methodAction==TransactionSpecification.COMMITTRANSACTION_Call && TransactionSpecification.state==TransactionSpecification.TransactionOpened && true) ==> \result==id9) && 
		((methodAction==TransactionSpecification.ABORTTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id10 && true) ==> \result==NoTransaction) && 
		((methodAction==TransactionSpecification.BEGINTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id7 && true) ==> \result==TransactionOpened) && 
		((methodAction==TransactionSpecification.COMMITTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id9 && true) ==> \result==NoTransaction)  ; @*/ 
	/*@ ensures (!(methodAction==TransactionSpecification.BEGINTRANSACTION_Call && TransactionSpecification.state==TransactionSpecification.NoTransaction && true) && 
			!(methodAction==TransactionSpecification.ABORTTRANSACTION_Call && TransactionSpecification.state==TransactionSpecification.TransactionOpened && true) && 
			!(methodAction==TransactionSpecification.COMMITTRANSACTION_Call && TransactionSpecification.state==TransactionSpecification.TransactionOpened && true) && 
			!(methodAction==TransactionSpecification.ABORTTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id10 && true) && 
			!(methodAction==TransactionSpecification.BEGINTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id7 && true) && 
			!(methodAction==TransactionSpecification.COMMITTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id9 && true) ) ==> \result==state ; @*/ 
	public static /*@pure@*/ int goNext(int methodAction);

}