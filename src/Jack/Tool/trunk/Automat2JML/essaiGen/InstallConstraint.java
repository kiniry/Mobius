
/* Generated automatically on Fri Jul 08 17:48:16 CEST 2005*/

package essaiGen ; 


public class InstallConstraint { 


	//Local variables
	//(None to be added)


	//State Definition
	/*@ public final static ghost int INSTALLED = 0 ; @*/ 
	/*@ public final static ghost int LOADED = 1 ; @*/ 
	/*@ public final static ghost int Registered = 2 ; @*/ 
	/*@ public final static ghost int Registering1 = 3 ; @*/ 
	/*@ public final static ghost int Registering2 = 4 ; @*/ 
	/*@ public final static ghost int Unregistered = 5 ; @*/ 
	/*@ public static int state = LOADED ; @*/ 

	//nodes invariants
	/*@ static invariant (state==INSTALLED || 
	              state==LOADED || 
	              state==Registered || 
	              state==Registering1 || 
	              state==Registering2 || 
	              state==Unregistered ); 
	@*/ 
	//@ static invariant (state==INSTALLED) ==> (GlobalDefinitionClass.registered==true) ; 
	//@ static invariant (state==LOADED) ==> (GlobalDefinitionClass.registered := false) ; 


	/*	Modification function of the Automaton   */
	 /*@ public final static ghost int INSTALL_Call = 0; @*/ 
	 /*@ public final static ghost int INSTALL_NT = 1; @*/ 
	 /*@ public final static ghost int INSTALL_ET = 2; @*/ 
	 /*@ public final static ghost int REGISTER1_Call = 3; @*/ 
	 /*@ public final static ghost int REGISTER1_NT = 4; @*/ 
	 /*@ public final static ghost int REGISTER1_ET = 5; @*/ 
	 /*@ public final static ghost int REGISTER2_Call = 6; @*/ 
	 /*@ public final static ghost int REGISTER2_NT = 7; @*/ 
	 /*@ public final static ghost int REGISTER2_ET = 8; @*/ 


	//@ modifies \nothing ; 
	/*@ ensures ((methodAction==InstallConstraint.INSTALL_Call && InstallConstraint.state==InstallConstraint.LOADED && true) ==> \result==Unregistered) && 
		((methodAction==InstallConstraint.INSTALL_NT && InstallConstraint.state==InstallConstraint.Registered && true) ==> \result==INSTALLED) && 
		((methodAction==InstallConstraint.REGISTER1_NT && InstallConstraint.state==InstallConstraint.Registering1 && true) ==> \result==Registered) && 
		((methodAction==InstallConstraint.REGISTER1_ET && InstallConstraint.state==InstallConstraint.Registering1 && true) ==> \result==Unregistered) && 
		((methodAction==InstallConstraint.REGISTER2_NT && InstallConstraint.state==InstallConstraint.Registering2 && true) ==> \result==Registered) && 
		((methodAction==InstallConstraint.REGISTER2_ET && InstallConstraint.state==InstallConstraint.Registering2 && true) ==> \result==Unregistered) && 
		((methodAction==InstallConstraint.INSTALL_NT && InstallConstraint.state==InstallConstraint.Unregistered && true) ==> \result==LOADED) && 
		((methodAction==InstallConstraint.INSTALL_ET && InstallConstraint.state==InstallConstraint.Unregistered && true) ==> \result==LOADED) && 
		((methodAction==InstallConstraint.REGISTER1_Call && InstallConstraint.state==InstallConstraint.Unregistered && true) ==> \result==Registering1) && 
		((methodAction==InstallConstraint.REGISTER2_Call && InstallConstraint.state==InstallConstraint.Unregistered && true) ==> \result==Registering2)  ; @*/ 
	/*@ ensures (!(methodAction==InstallConstraint.INSTALL_Call && InstallConstraint.state==InstallConstraint.LOADED && true) && 
			!(methodAction==InstallConstraint.INSTALL_NT && InstallConstraint.state==InstallConstraint.Registered && true) && 
			!(methodAction==InstallConstraint.REGISTER1_NT && InstallConstraint.state==InstallConstraint.Registering1 && true) && 
			!(methodAction==InstallConstraint.REGISTER1_ET && InstallConstraint.state==InstallConstraint.Registering1 && true) && 
			!(methodAction==InstallConstraint.REGISTER2_NT && InstallConstraint.state==InstallConstraint.Registering2 && true) && 
			!(methodAction==InstallConstraint.REGISTER2_ET && InstallConstraint.state==InstallConstraint.Registering2 && true) && 
			!(methodAction==InstallConstraint.INSTALL_NT && InstallConstraint.state==InstallConstraint.Unregistered && true) && 
			!(methodAction==InstallConstraint.INSTALL_ET && InstallConstraint.state==InstallConstraint.Unregistered && true) && 
			!(methodAction==InstallConstraint.REGISTER1_Call && InstallConstraint.state==InstallConstraint.Unregistered && true) && 
			!(methodAction==InstallConstraint.REGISTER2_Call && InstallConstraint.state==InstallConstraint.Unregistered && true) ) ==> \result==state ; @*/ 
	public static /*@pure@*/ int goNext(int methodAction);

}