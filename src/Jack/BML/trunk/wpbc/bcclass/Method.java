/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

import java.util.HashMap;
import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.generic.CodeExceptionGen;

import org.apache.bcel.generic.AALOAD;
import org.apache.bcel.generic.AASTORE;
import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.ARRAYLENGTH;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.ArithmeticInstruction;
import org.apache.bcel.generic.ArrayInstruction;
import org.apache.bcel.generic.BALOAD;
import org.apache.bcel.generic.BASTORE;
import org.apache.bcel.generic.CALOAD;
import org.apache.bcel.generic.CASTORE;
import org.apache.bcel.generic.CHECKCAST;
import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConstantPushInstruction;
import org.apache.bcel.generic.ConversionInstruction;
import org.apache.bcel.generic.DALOAD;
import org.apache.bcel.generic.DASTORE;
import org.apache.bcel.generic.ExceptionThrower;
import org.apache.bcel.generic.FALOAD;
import org.apache.bcel.generic.FASTORE;
import org.apache.bcel.generic.GETFIELD;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.IALOAD;
import org.apache.bcel.generic.IASTORE;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.IfInstruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.JsrInstruction;
import org.apache.bcel.generic.LALOAD;
import org.apache.bcel.generic.LASTORE;
import org.apache.bcel.generic.LCMP;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MULTIANEWARRAY;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.NEW;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.NOP;
import org.apache.bcel.generic.PUTFIELD;
import org.apache.bcel.generic.RET;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.SALOAD;
import org.apache.bcel.generic.SASTORE;
import org.apache.bcel.generic.StackInstruction;
import org.apache.bcel.generic.TypedInstruction;

import specification.ExceptionalPostcondition;
import utils.Util;

import formula.Formula;

import bcexpression.Expression;
import bcexpression.javatype.JavaType;
import bytecode.BCATHROW;
import bytecode.BCConditionalBranch;
import bytecode.BCGOTO;
import bytecode.BCInstruction;
import bytecode.BCJSR;
import bytecode.BCNOP;
import bytecode.BCRET;
import bytecode.BCStackInstruction;
import bytecode.BCTypeRETURN;
import bytecode.Trace;
import bytecode.arithmetic.BCLCMP;
import bytecode.objectmanipulation.BCANEWARRAY;
import bytecode.objectmanipulation.BCARRAYLENGTH;
import bytecode.objectmanipulation.BCCheckCastInstruction;
import bytecode.objectmanipulation.BCGETFIELD;
import bytecode.objectmanipulation.BCINSTANCEOF;
import bytecode.objectmanipulation.BCINVOKEInstruction;
import bytecode.objectmanipulation.BCLDC;
import bytecode.objectmanipulation.BCLDC2_W;
import bytecode.objectmanipulation.BCMULTIANEWARRAY;
import bytecode.objectmanipulation.BCNEW;
import bytecode.objectmanipulation.BCNEWARRAY;
import bytecode.objectmanipulation.BCPUTFIELD;
import bytecode.objectmanipulation.BCTypeALOAD;
import bytecode.objectmanipulation.BCTypeASTORE;
import bytecode.loadstoreinstruction.BCIINC;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Method {
	private BCInstruction[] code;
	private Trace trace;

	private ExceptionalPostcondition excPostcondition;
	private Formula precondition;
	private Formula postcondition;
	private Expression[] assignables;
	private Vector pogs;

	private CodeExceptionGen[] excHandlers;
	private BCLocalVariable[] localVariabes;
	private Attribute[] codeAttributes;

	public Method(MethodGen _mg, ConstantPoolGen _cp) {
		setCode(code);
		setLocalVariables(_mg.getLocalVariables(), _cp);
		code = Method.wrapByteCode(_mg.getInstructionList(), _mg, _cp);
		excHandlers = _mg.getExceptionHandlers();
		codeAttributes = _mg.getCodeAttributes();

	}

	/**
	 * @param gens
	 */
	private void setLocalVariables(
		LocalVariableGen[] gens,
		ConstantPoolGen _cp) {
		if (gens == null) {
			return;
		}
		if (gens.length <= 0) {
			return;
		}
		localVariabes = new BCLocalVariable[gens.length];
		for (int i = 0; i < localVariabes.length; i++) {
			localVariabes[i] = new BCLocalVariable(gens[i]);
		}

	}

	public BCLocalVariable getLocalVariableAtIndex(int i) {
		return localVariabes[i];
	}

	/**
	 * @return
	 */
	public BCInstruction[] getCode() {
		return code;
	}

	/**
	 * @return the predicate that must be true in the state after the execution of the method
	 */
	public ExceptionalPostcondition getExceptionalPostcondition() {
		return excPostcondition;
	}

	/**
	 * @return the predicate that must be true in the state after the execution of the method
	 */
	public Formula getPostcondition() {
		return postcondition;
	}

	/**
	 * @return the predicate that must be true in the state before the execution of the method
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
	public void setExcPostcondition(HashMap hm) {
		//TODO
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

	/**
	 * called by outside ? once the Method object is initialised
	 * @param _mg
	 */
	protected void initTrace(MethodGen _mg) {
		if (trace != null) {
			return;
		}
		setTrace(new Trace(code, _mg));
	}

	public static BCInstruction[] wrapByteCode(
		InstructionList _il,
		MethodGen _mg,
		ConstantPoolGen _cp) {
		InstructionHandle[] _iharr = _il.getInstructionHandles();
		BCInstruction[] _bc = new BCInstruction[_iharr.length];
		for (int i = 0; i < _iharr.length; i++) {
			if (_iharr[i].getInstruction() instanceof ReturnInstruction) {
				_bc[i] = new BCTypeRETURN(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof RET) {
				_bc[i] = new BCRET(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof GotoInstruction) {
				_bc[i] = new BCGOTO(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof ATHROW) {
				_bc[i] = new BCATHROW(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof JsrInstruction) {
				_bc[i] = new BCJSR(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof IfInstruction) {
				_bc[i] = new BCConditionalBranch(_iharr[i]);
			} else if (
				(_iharr[i].getInstruction() instanceof ArithmeticInstruction)
					&& (_iharr[i].getInstruction() instanceof ExceptionThrower)) {
				JavaType _type =
					JavaType.getJavaRefType(
						((TypedInstruction) _iharr[i].getInstruction())
							.getType(_cp)
							.getSignature());

				//				_bc[i] = new  BCArithmeticInstructionWithException(_iharr[i], _type);
			} else if (
				_iharr[i].getInstruction() instanceof ArithmeticInstruction) {
				JavaType _type =
					JavaType.getJavaRefType(
						((TypedInstruction) _iharr[i].getInstruction())
							.getType(_cp)
							.getSignature());
				//				_bc[i] = new  BCArithmeticInstruction(_iharr[i], _type);
			} else if (
				_iharr[i].getInstruction()
					instanceof ConstantPushInstruction) {
				//				_bc[i] = new BCConstantPUSHInstruction(_iharr[i]);
			} else if (
				_iharr[i].getInstruction() instanceof ConversionInstruction) {
				//_bc[i] = new BCConversionInstruction(_iharr[i]);
			} else if (
				_iharr[i].getInstruction() instanceof StackInstruction) {
				_bc[i] = new BCStackInstruction(_iharr[i]);
			} else if (
				_iharr[i].getInstruction() instanceof ArrayInstruction) {
				JavaType _type =
					JavaType.getJavaRefType(
						((TypedInstruction) _iharr[i].getInstruction())
							.getType(_cp)
							.getSignature());
				if ((_iharr[i].getInstruction() instanceof AALOAD)
					|| (_iharr[i].getInstruction() instanceof BALOAD)
					|| (_iharr[i].getInstruction() instanceof CALOAD)
					|| (_iharr[i].getInstruction() instanceof LALOAD)
					|| (_iharr[i].getInstruction() instanceof DALOAD)
					|| (_iharr[i].getInstruction() instanceof FALOAD)
					|| (_iharr[i].getInstruction() instanceof SALOAD)
					|| (_iharr[i].getInstruction() instanceof IALOAD)) {
					_bc[i] = new BCTypeALOAD(_iharr[i], _type);
				}
				if ((_iharr[i].getInstruction() instanceof AASTORE)
					|| (_iharr[i].getInstruction() instanceof BASTORE)
					|| (_iharr[i].getInstruction() instanceof CASTORE)
					|| (_iharr[i].getInstruction() instanceof LASTORE)
					|| (_iharr[i].getInstruction() instanceof DASTORE)
					|| (_iharr[i].getInstruction() instanceof FASTORE)
					|| (_iharr[i].getInstruction() instanceof SASTORE)
					|| (_iharr[i].getInstruction() instanceof IASTORE)) {
					_bc[i] = new BCTypeASTORE(_iharr[i], _type);
				}
				//cp instructions 
			} else if (_iharr[i].getInstruction() instanceof CPInstruction) {
				JavaType _type =
					JavaType.getJavaRefType(
						((TypedInstruction) _iharr[i].getInstruction())
							.getType(_cp)
							.getSignature());
				if (_iharr[i].getInstruction() instanceof InvokeInstruction) {
					_bc[i] = new BCINVOKEInstruction(_iharr[i], _type);
				} else if (_iharr[i].getInstruction() instanceof PUTFIELD) {
					_bc[i] = new BCPUTFIELD(_iharr[i], _type);
				} else if (_iharr[i].getInstruction() instanceof GETFIELD) {
					_bc[i] = new BCGETFIELD(_iharr[i], _type);
				} else if (_iharr[i].getInstruction() instanceof CHECKCAST) {
					_bc[i] = new BCCheckCastInstruction(_iharr[i], _type);
				} else if (_iharr[i].getInstruction() instanceof LDC) {
					_bc[i] = new BCLDC(_iharr[i], _type);
				} else if (_iharr[i].getInstruction() instanceof LDC2_W) {
					_bc[i] = new BCLDC2_W(_iharr[i], _type);
				} else if (_iharr[i].getInstruction() instanceof NEW) {
					_bc[i] = new BCNEW(_iharr[i], _type);
				} else if (_iharr[i].getInstruction() instanceof ANEWARRAY) {
					_bc[i] = new BCANEWARRAY(_iharr[i], _type);
				} else if (
					_iharr[i].getInstruction() instanceof MULTIANEWARRAY) {
					_bc[i] = new BCMULTIANEWARRAY(_iharr[i], _type);
				} else if (_iharr[i].getInstruction() instanceof INSTANCEOF) {
					_bc[i] = new BCINSTANCEOF(_iharr[i], _type);
				}
			} else if (_iharr[i].getInstruction() instanceof NEWARRAY) {
				JavaType _type =
					JavaType.getJavaRefType(
						((TypedInstruction) _iharr[i].getInstruction())
							.getType(_cp)
							.getSignature());
				_bc[i] = new BCNEWARRAY(_iharr[i], _type);
			} else if (_iharr[i].getInstruction() instanceof ARRAYLENGTH) {
				_bc[i] = new BCARRAYLENGTH(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof LCMP) {
				_bc[i] = new BCLCMP(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof IINC) {
			//	_bc[i] = new BCIINC(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof NOP) {
				_bc[i] = new BCNOP(_iharr[i]);
			}
			_bc[i].setBCIndex(i);
			//set the bytecode command at the previous position and at the next positition
			if (i > 0) {
				_bc[i].setPrev(_bc[i - 1]);
				_bc[i - 1].setNext(_bc[i]);
			}
		}
		_bc = Util.setTargets(_bc, _mg);
		return _bc;
	}
}
