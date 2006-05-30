/*
 * Created on Aug 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode;


import java.util.Enumeration;
import java.util.Vector;


import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bytecode.branch.BCConditionalBranch;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.vcg.VCGPath;


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
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return null;
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition)  {
		return null;
	}
	
	
	private VCGPath addFormula(VCGPath _wp ) {
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
	 * 
	 * returns the vector of weakest preconditions for a path
	 * @return
	 */
	public Vector getWp() {
		return wp;
		/*if (wp == null) {
			return null;
		}
		Enumeration eWp = wp.elements();
		Formula wps = Predicate0Ar.TRUE;
		while (eWp.hasMoreElements() ) {
			Formula f = (Formula)eWp.nextElement();
			wps = Formula.getFormula(wps, f, Connector.AND);
		}
		return wps;*/
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

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		VCGPath wp = instr.wp(config, vcs, _exc); 
		addFormula(wp);
		return wp;
	}		
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public VCGPath wpBranch(VCGPath _normal_Postcondition, ExsuresTable _exc_Postcondition)  {
		VCGPath wp= ( (BCConditionalBranch)instr).wpBranch(null, _normal_Postcondition, _exc_Postcondition); 
		addFormula(wp);
		return wp;
	}
	
}
