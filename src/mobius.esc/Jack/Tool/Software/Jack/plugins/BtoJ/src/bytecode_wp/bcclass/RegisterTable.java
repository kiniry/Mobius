/*
 * Created on Jan 27, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode_wp.bcclass;

import java.util.Vector;

import bytecode_wp.bcexpression.BCLocalVariable;

/**
 * @author Mariela
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class RegisterTable {
	 private Vector registers;
	 
	 public void addRegister(BCLocalVariable lv ) {
	 	if (registers == null) {
	 			registers = new Vector();
	 	}
	 	registers.add(lv);
	 } 
	 
	 public BCLocalVariable[] getLocalVariables() {
	 	if ( registers == null ) {
	 		return null;
	 	}
	 	BCLocalVariable[] lv = new BCLocalVariable[registers.size()];
	 	for (int i = 0; i < lv.length; i++) {
	 		lv[i] = (BCLocalVariable)registers.get( i);
	 	}
	 	return lv;
	 }
	 
	 /**
	  * still this method doesnot take into account that a register 
	  * may store different values at different points of the program
	  * 
	  * @param ind
	  * @return the local variable object with this index
	  */
	 public BCLocalVariable getLocalVariableAtIndex(int ind) {
	 	if (registers == null) {
	 		return null;
	 	}
	 	if ( (ind < 0 ) || (registers.size() <= ind)  ) {
	 		return null;
	 	}
	 	for (int i = 0; i < registers.size(); i++) {
	 		BCLocalVariable lv = (BCLocalVariable)registers.get( i);
	 		if (lv.getIndex() == ind) {
	 			return lv;
	 		}
	 	}
	 	return null;
	 }
	 
	 public int getLength() {
 		if (registers == null) {
 				return 0;
 		}
 		return registers.size();
	 }
	 
	 /**
	  * returns true if a local variable with the  index <code> ind </code>
	  * already exists in the list of local variables 
	  * Otherwise returns false
	  * used when the register table is initialized
	  * @param lv
	  */
	 public boolean searchForDuplicate(int ind) {
		 if (registers == null){
			 return false;
		 }
		 for (int i = 0; i < registers.size(); i++) {
		 		BCLocalVariable _lv = (BCLocalVariable)registers.get( i);
		 		if (_lv.getIndex() == ind) {
		 			return true;
		 		}
		 }
		 return false;		 
	 }
	 
}
