/*
 * Created on Feb 27, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Enumeration;
import java.util.Vector;

import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCGotoInstruction extends BCUnconditionalBranch implements EndBlock{
	
	private Formula  wp;
	/**
	 * @param _branchInstruction
	 */
	public BCGotoInstruction(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}
	
	public void setWP(Formula _wp) {
	
	}
	
	public Formula wp() {
		Enumeration targets = getTargetBlocks().elements();
		return null;
	}

}
