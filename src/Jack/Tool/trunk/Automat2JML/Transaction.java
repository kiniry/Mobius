


/*
 * Created on Apr 15, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
/**
 * @author tdupont
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */


//@ import essaiGen.*;

public class Transaction {

	
	private boolean transactionRunning = false;
	
	
	/*@ requires    Property1.state==Property1.ZeroTransaction &&
	Property2.state==Property2.Idle &&
	Property3.state==Property3.NormalExecution &&
	Property4.state==Property4.Callable &&
	Property5.state==Property5.Callable &&
	GlobalDefinitionClass.allowCloseTransaction == false &&
	GlobalDefinitionClass.allowBeginTransaction == true &&
	GlobalDefinitionClass.a == true &&
	Property1.x ==  0 &&
	Property1.y ==  0 ; 
	@*/
	public void TransactionSimulation(){
		
		for(int i=0; i<10 ; i++)
		{
			try { beginTransaction();}catch(Exception e) { System.err.println("BOOM !");}
			closeTransaction();
		}
	}
	
	
	
	
	//-------------------------------------------
	// Method to be verified
	//-------------------------------------------
		
   
	/*@ requires (Property1.state==Property1.ZeroTransaction && (GlobalDefinitionClass.a==true) )  ; @*/ 
	/*@ requires (Property2.state==Property2.Idle && (true) ) || 
	(Property2.state==Property2.Running && (true) )  ; @*/ 
	/*@ requires (Property4.state==Property4.Callable && (! GlobalDefinitionClass.allowBeginTransaction) )  ; @*/ 
	/*@ modifies  transactionRunning, Property1.x , Property1.y , Property1.state, Property2.state, Property4.state; @*/ 
	/*@ ensures (\old(Property1.state)==Property1.ZeroTransaction && (true) ) ==> (Property1.state==Property1.OneTransaction) ; @*/ 
	/*@ ensures (\old(Property2.state)==Property2.Idle && (true) ) ==> (Property2.state==Property2.Idle) ; @*/ 
	/*@ exsures (Exception e) (\old(Property2.state)==Property2.Idle && (true) ) ==> (Property2.state==Property2.Idle) ; @*/ 
	public void beginTransaction() throws Exception{
		boolean __INTERNAL_TEST = false; 
		/* Entry Actions */
		/*@ set Property1.state=Property1.goNext(Property1.BEGINTRANSACTION_Call); 
		set Property2.state=Property2.goNext(Property2.BEGINTRANSACTION_Call); 
		set Property4.state=Property4.goNext(Property4.BEGINTRANSACTION_Call); @*/ 
		try{
			/*-- Method Body --*/
			if (transactionRunning==false) {
				transactionRunning = true ;
				return;
			}
			else{	
				throw new Exception();
			}
			/*--- End Body ---*/
		}
		catch(Exception e){ 
			__INTERNAL_TEST = true; 
			/* Exceptional Exit Actions */
			/*@ set Property2.state=Property2.goNext(Property2.BEGINTRANSACTION_ET); @*/ 
			throw e;
		} 
		finally{ 
			/* Normal Exit Actions */
			if (!__INTERNAL_TEST ){
				/*@ Property1.x(Property1.BEGINTRANSACTION_NT); 
				Property1.y(Property1.BEGINTRANSACTION_NT); 
				set Property1.state=Property1.goNext(Property1.BEGINTRANSACTION_NT); 
				set Property2.state=Property2.goNext(Property2.BEGINTRANSACTION_NT); 
				set Property4.state=Property4.goNext(Property4.BEGINTRANSACTION_NT); @*/ 
			}
		}
	}

	/*@ requires (Property1.state==Property1.OneTransaction && (true) )  ; @*/ 
	/*@ requires (Property5.state==Property5.Callable && (! GlobalDefinitionClass.allowCloseTransaction) )  ; @*/ 
	/*@ modifies  transactionRunning, Property1.x , Property1.y , Property1.state, Property5.state; @*/ 
	/*@ ensures (\old(Property1.state)==Property1.OneTransaction && (true) ) ==> (Property1.state==Property1.ZeroTransaction) ; @*/ 
	public void closeTransaction() { //beglongs to call Transaction
		boolean __INTERNAL_TEST = false; 
		/* Entry Actions */
		/*@ set Property1.state=Property1.goNext(Property1.CLOSETRANSACTION_Call); 
		set Property5.state=Property5.goNext(Property5.CLOSETRANSACTION_Call); @*/ 
		try{
			/*-- Method Body --*/
			transactionRunning = false;
			/*--- End Body ---*/
		}
		catch(Exception e){ 
			__INTERNAL_TEST = true; 
			/* Exceptional Exit Actions */
		} 
		finally{ 
			/* Normal Exit Actions */
			if (!__INTERNAL_TEST ){
				/*@ Property1.x(Property1.CLOSETRANSACTION_NT); 
				Property1.y(Property1.CLOSETRANSACTION_NT); 
				set Property1.state=Property1.goNext(Property1.CLOSETRANSACTION_NT); 
				set Property5.state=Property5.goNext(Property5.CLOSETRANSACTION_NT); @*/ 
			}
		}
	}
	
	
	
}





