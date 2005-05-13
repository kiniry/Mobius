


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
		
   
   
    /*@
       requires Property1.state==Property1.ZeroTransaction&&
                GlobalDefinitionClass.a==true&&
                Property2.state==Property2.Idle&&
                true||
                Property2.state==Property2.Running&&
                true&&
                Property4.state==Property4.Callable&&
                ! GlobalDefinitionClass.allowBeginTransaction;
       modifies Property4.state,
          Property2.state,
          Property1.state,
          Property1.y,
          Property1.x;
       ensures \old(Property1.state)==Property1.ZeroTransaction&&
               true==>Property1.state==Property1.OneTransaction&&
               \old(Property2.state)==Property2.Idle&&
               true==>Property2.state==Property2.Idle;
    @*/
	public void beginTransaction() throws Exception{
		/* Entry Actions */
		boolean __INTERNAL_TEST = false;
		try {
			
			/* INITIAL FUNCTION BODY */
			if (transactionRunning==false) {
				transactionRunning = true ;
				return;
			}
			else{	
			
				throw new Exception();
			}
			/*-----------------------*/
		}
		catch(Exception e){
			__INTERNAL_TEST = true;
			/* Normal Exit Actions */
			throw e;
		}
		finally{
			if (__INTERNAL_TEST==false){
				/* Normal Exit Actions */
			}
		}
	}


    /*@
       requires Property1.state==Property1.OneTransaction&&
                true&&
                Property5.state==Property5.Callable&&
                ! GlobalDefinitionClass.allowCloseTransaction;
       modifies Property1.x,
          Property1.y,
          Property1.state,
          Property5.state;
       ensures \old(Property1.state)==Property1.OneTransaction&&
               true==>Property1.state==Property1.ZeroTransaction;
    @*/
	public void closeTransaction() { //beglongs to call Transaction
		/* Entry Actions */
		boolean __INTERNAL_TEST = false;
		try {
			
			transactionRunning = false;
		}
		catch(Exception e){
			__INTERNAL_TEST = true;
		}
		finally{
			if (__INTERNAL_TEST==false){
				/* Normal Exit Actions */
			}
		}
	}
	
	
	
}





