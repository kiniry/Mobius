/*
 * Created on Aug 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;


import java.util.Enumeration;
import java.util.Vector;

import bcclass.attributes.ExsuresTable;
import bytecode.branch.BCConditionalBranch;
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;


/**
 * @author mpavlova
 *
 *This class models a program entry point , entry points to subroutines and entry points to exception handlers
 */
public class EntryPoint extends BCInstruction {
	/**
	 * the wrapped instruction that appears to be an entry point 
	 */
	private BCInstruction instr;
	
	private Vector wp;
	
	
	public EntryPoint(BCInstruction _instr) {
				instr = _instr;
				setBytecode (_instr.getBytecode());
				instructionHandle = _instr.getInstructionHandle();
				setNext(_instr.getNext());
				setPrev(_instr.getPrev());
				setBCIndex(_instr.getBCIndex());
				setTargeters(_instr.getTargeters());
				setPosition(_instr.getPosition());

				//actualise the values in the previous and the next instruction
				BCInstruction prev = _instr.getPrev();
				if (prev != null) {
					prev.setNext(this);
				}
				BCInstruction next = _instr.getNext();
				if (next != null) {
					next.setPrev(this);
				}
	}

	public BCInstruction getWrappedInstruction() {
		return instr;
	}
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp = instr.wp(_normal_Postcondition, _exc_Postcondition); 
		addFormula(wp);
		return wp;
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition)  {
		Formula wp= ( (BCConditionalBranch)instr).wpBranch(_normal_Postcondition, _exc_Postcondition); 
		addFormula(wp);
		return wp;
	}
	
	
	private Formula addFormula(Formula _wp ) {
		if (this.wp == null) {
			this.wp = new Vector();
		}
		wp.add(_wp);
		
		return _wp;
	} 
	
	
	public String toString() {
		return "ENTRY POINT " + instr;	
	}
	
	/**
	 * @return
	 */
	public Formula getWp() {
		if (wp == null) {
			return null;
		}
		Enumeration eWp = wp.elements();
		Formula wps = Predicate0Ar.TRUE;
		while (eWp.hasMoreElements() ) {
			Formula f = (Formula)eWp.nextElement();
			wps = Formula.getFormula(wps, f, Connector.AND);
		}
		return wps;
	}
	
	/**
	 * 
	 * @return a vector of the weakest preconditions for
	 * every path
	 */
	public Vector getWps() {
		return wp;
	}

	/**
	 * @return
	 */
	public void initWP() {
		wp = null;
	}
	
}
