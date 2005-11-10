
/* Generated automatically on Fri Jul 08 17:48:16 CEST 2005*/

package essaiGen ; 


public class GlobalDefinitionClass { 


	//Insertion of the system static variables
	/*@ public static ghost boolean registered =  false ; 
	/*@ public static ghost boolean performingTransaction =  false ; 
	/*@ public static ghost boolean isSelected =  false ; 


	//registered
	//@ modifies registered; 
	/*@ ensures (methodAction==InstallConstraint.REGISTER1_NT && InstallConstraint.state==InstallConstraint.Registering1 && true) ==> registered == \old(true) @*/;
	/*@ ensures (methodAction==InstallConstraint.REGISTER2_NT && InstallConstraint.state==InstallConstraint.Registering2 && true) ==> registered == \old(true) @*/;
	/*@ ensures (
		!(methodAction==InstallConstraint.REGISTER1_NT && InstallConstraint.state==InstallConstraint.Registering1 && true) && 
		!(methodAction==InstallConstraint.REGISTER2_NT && InstallConstraint.state==InstallConstraint.Registering2 && true) ) ==> registered==\old(registered); @*/ 
	 public static void  registered(int methodAction);

	//performingTransaction
	//@ modifies performingTransaction; 
	/*@ ensures (methodAction==TransactionSpecification.ABORTTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id10 && true) ==> performingTransaction == \old(false) @*/;
	/*@ ensures (methodAction==TransactionSpecification.BEGINTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id7 && true) ==> performingTransaction == \old(true) @*/;
	/*@ ensures (methodAction==TransactionSpecification.COMMITTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id9 && true) ==> performingTransaction == \old(false) @*/;
	/*@ ensures (
		!(methodAction==TransactionSpecification.ABORTTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id10 && true) && 
		!(methodAction==TransactionSpecification.BEGINTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id7 && true) && 
		!(methodAction==TransactionSpecification.COMMITTRANSACTION_NT && TransactionSpecification.state==TransactionSpecification.id9 && true) ) ==> performingTransaction==\old(performingTransaction); @*/ 
	 public static void  performingTransaction(int methodAction);

}