/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.generic.CodeExceptionGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;

import utils.Util;

import formula.Formula;

import bcexpression.Expression;
import bytecode.BCInstruction;
import bytecode.ByteCode;
import bytecode.Trace;


/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Method {
	private BCInstruction[] code;
	private Trace trace;
	
	private Formula postcondition;	
	private Formula precondition;
	private Expression[] assignables;
	private Vector pogs;
	
	
	private CodeExceptionGen[] excHandlers;
	private LocalVariableGen[] localVariabes;
	private Attribute[] codeAttributes;
	
	
	
	public Method(BCInstruction[] code) {
		setCode(code);
	}

	public Method(BCInstruction[] code, MethodGen _mg) {
		setCode(code);
		excHandlers = _mg.getExceptionHandlers();
		localVariabes = _mg.getLocalVariables();
		codeAttributes = _mg.getCodeAttributes();
	}
	
	public Method(InstructionList code, MethodGen _mg) {
		BCInstruction[] _bci = Util.wrapByteCode(code,_mg);
		setCode(_bci);
		excHandlers = _mg.getExceptionHandlers();
		localVariabes = _mg.getLocalVariables();
		codeAttributes = _mg.getCodeAttributes();
	}
	/**
	 * @return
	 */
	public BCInstruction[] getCode() {
		return code;
	}

	/**
	 * @return
	 */
	public Formula getPostcondition() {
		return postcondition;
	}

	/**
	 * @return
	 */
	public Formula getPrecondition() {
		return precondition;
	}

	/**
	 * @return
	 */
	public Trace getTrace() {
		return trace;
	}

	/**
	 * @param codes
	 */
	public void setCode(BCInstruction[] codes) {
		code = codes;
	}

	/**
	 * @param formula
	 */
	public void setPostcondition(Formula formula) {
		postcondition = formula;
	}

	/**
	 * @param formula
	 */
	public void setPrecondition(Formula formula) {
		precondition = formula;
	}

	/**
	 * @param trace
	 */
	private void setTrace(Trace trace) {
		this.trace = trace;
	}

	void initTrace() {
		if (trace != null) {
			return;
		}
		setTrace (new Trace( code) );
	}
}
