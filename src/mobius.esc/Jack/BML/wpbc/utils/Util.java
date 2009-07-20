/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package utils;
import java.util.Collection;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionList;

import formula.Formula;


import bcclass.BCClass;
import bcclass.BCMethod;
import bytecode.BCInstruction;

import bytecode.branch.BCJumpInstruction;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Util {
	public static boolean DUMP = true;
	
	/**
	 * updates the instruction - some of the instructions are wrapped in other objects , e.g. -loop starts and ends, and start of exception handlers
	 * @param _bc
	 * @param update
	 */
	public static void update(BCInstruction[] _bc, BCInstruction update) {
		int positionToUpdateWith = update.getPosition();
		int bcIndexToUpdate = update.getBCIndex();
		// if it is the same object no need to update
		if (_bc[ bcIndexToUpdate ] != update) {
			_bc[ bcIndexToUpdate ] = update;
		}
	}
	
	public static BCInstruction[] setTargets(BCInstruction[] _bc)  {
		for (int i = 0; i < _bc.length; i++) {		
			if (_bc[i] instanceof BCJumpInstruction) {
				BCInstruction _ih = null;
				int offset;
				offset = ((BCJumpInstruction) _bc[i]).getTargetPosition();
				_ih = getBCInstructionAtPosition(_bc, offset);
				((BCJumpInstruction) _bc[i]).setTarget(_ih);
				_ih.addTargeter(_bc[i]);
			}
		}
		return _bc;
	}
	

	/**
	 * @param i
	 * @return the
	 */
	public static BCInstruction getBCInstructionAtPosition(BCInstruction[] _b,
			int offset) {
		for (int i = 0; i < _b.length; i++) {
			if (_b[i].getPosition() == offset) {
				return _b[i];
			}
		}
		return null;
	}
	
	public static void  dump(BCInstruction[] instrs ){
		
		if (instrs == null) {
			return;
		}
		for (int i =0; i < instrs.length; i++) {
			System.out.println(instrs[i]);
		}
	
	}	
	public static void  dump(InstructionList list ){
		Instruction[] instrs = list.getInstructions();
		if (instrs == null) {
			return;
		}
		for (int i =0; i < instrs.length; i++) {
			System.out.println(instrs[i]);
		}
	
	}	
	public static void dump(String s) {
		if (DUMP) {
			System.out.println(s);
		}
	}
	
	public static void   dump(Vector v ) {
		Enumeration en = v.elements();
		Formula b;
		while (en.hasMoreElements()) {
			b =(Formula)en.nextElement();
			Util.dump(b.toString());
		}
	} 
	
	public static void dumpMethods(BCClass clazz) {
		Iterator c = clazz.getMethodKeys().iterator();
		while (c.hasNext()) { 
			String m = (String)c.next();
			Util.dump(m);
		}
		
	}
}
