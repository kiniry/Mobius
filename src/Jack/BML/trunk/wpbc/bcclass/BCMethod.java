/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;
import java.util.HashMap;

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
import org.apache.bcel.generic.ACONST_NULL;
import org.apache.bcel.generic.BIPUSH;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConversionInstruction;
import org.apache.bcel.generic.DALOAD;
import org.apache.bcel.generic.DASTORE;
import org.apache.bcel.generic.DUP;
import org.apache.bcel.generic.DUP2;
import org.apache.bcel.generic.DUP2_X1;
import org.apache.bcel.generic.DUP2_X2;
import org.apache.bcel.generic.DUP_X1;
import org.apache.bcel.generic.DUP_X2;
import org.apache.bcel.generic.FALOAD;
import org.apache.bcel.generic.FASTORE;
import org.apache.bcel.generic.FieldOrMethod;
import org.apache.bcel.generic.GETFIELD;
import org.apache.bcel.generic.GETSTATIC;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.I2B;
import org.apache.bcel.generic.I2C;

import org.apache.bcel.generic.I2S;
import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.IALOAD;
import org.apache.bcel.generic.IAND;
import org.apache.bcel.generic.IASTORE;
import org.apache.bcel.generic.ICONST;
import org.apache.bcel.generic.IDIV;
import org.apache.bcel.generic.IFEQ;
import org.apache.bcel.generic.IFGE;
import org.apache.bcel.generic.IFGT;
import org.apache.bcel.generic.IFLE;
import org.apache.bcel.generic.IFLT;
import org.apache.bcel.generic.IFNE;
import org.apache.bcel.generic.IFNONNULL;
import org.apache.bcel.generic.IFNULL;
import org.apache.bcel.generic.IF_ACMPEQ;
import org.apache.bcel.generic.IF_ACMPNE;
import org.apache.bcel.generic.IF_ICMPEQ;
import org.apache.bcel.generic.IF_ICMPGE;
import org.apache.bcel.generic.IF_ICMPGT;
import org.apache.bcel.generic.IF_ICMPLE;
import org.apache.bcel.generic.IF_ICMPLT;
import org.apache.bcel.generic.IF_ICMPNE;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.IMUL;
import org.apache.bcel.generic.INEG;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.INVOKEINTERFACE;
import org.apache.bcel.generic.INVOKESPECIAL;
import org.apache.bcel.generic.INVOKESTATIC;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.IOR;
import org.apache.bcel.generic.IREM;
import org.apache.bcel.generic.ISHL;
import org.apache.bcel.generic.ISHR;
import org.apache.bcel.generic.ISUB;
import org.apache.bcel.generic.IUSHR;
import org.apache.bcel.generic.IXOR;
import org.apache.bcel.generic.IfInstruction;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.JsrInstruction;
import org.apache.bcel.generic.LALOAD;
import org.apache.bcel.generic.LASTORE;

import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LoadInstruction;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.LocalVariableInstruction;
import org.apache.bcel.generic.MULTIANEWARRAY;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.NEW;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.NOP;
import org.apache.bcel.generic.POP;
import org.apache.bcel.generic.POP2;
import org.apache.bcel.generic.PUTFIELD;
import org.apache.bcel.generic.PushInstruction;
import org.apache.bcel.generic.RET;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.SALOAD;
import org.apache.bcel.generic.SASTORE;
import org.apache.bcel.generic.SIPUSH;
import org.apache.bcel.generic.StackInstruction;
import org.apache.bcel.generic.StoreInstruction;
import org.apache.bcel.generic.TypedInstruction;
import utils.Util;
import formula.Connector;
import formula.Formula;
import bcclass.attributes.AssertTable;
import bcclass.attributes.BCExceptionTable;
import bcclass.attributes.ExceptionHandler;
import bcclass.attributes.ExsuresTable;
import bcclass.attributes.Postcondition;
import bcclass.attributes.Precondition;
import bcexpression.Expression;
import bcexpression.javatype.JavaObjectType;

import bcexpression.javatype.JavaType;
import bytecode.BCATHROW;
import bytecode.BCInstruction;
import bytecode.BCNOP;
import bytecode.BCRET;
import bytecode.BCTypeRETURN;

import bytecode.arithmetic.BCTypeADD;
import bytecode.arithmetic.BCTypeAND;
import bytecode.arithmetic.BCTypeDIV;
import bytecode.arithmetic.BCTypeMUL;
import bytecode.arithmetic.BCTypeNEG;
import bytecode.arithmetic.BCTypeOR;
import bytecode.arithmetic.BCTypeREM;
import bytecode.arithmetic.BCTypeSHL;
import bytecode.arithmetic.BCTypeSHR;
import bytecode.arithmetic.BCTypeSUB;
import bytecode.arithmetic.BCTypeUSHR;
import bytecode.arithmetic.BCTypeXOR;
import bytecode.block.Trace;
import bytecode.branch.BCGOTO;
import bytecode.branch.BCIFEQ;
import bytecode.branch.BCIFGE;
import bytecode.branch.BCIFGT;
import bytecode.branch.BCIFLE;
import bytecode.branch.BCIFLT;
import bytecode.branch.BCIFNE;
import bytecode.branch.BCIFNONNULL;
import bytecode.branch.BCIFNULL;
import bytecode.branch.BCIF_ACMPEQ;
import bytecode.branch.BCIF_ACMPNE;
import bytecode.branch.BCIF_ICMPEQ;
import bytecode.branch.BCIF_ICMPGE;
import bytecode.branch.BCIF_ICMPGT;
import bytecode.branch.BCIF_ICMPLE;
import bytecode.branch.BCIF_ICMPLT;
import bytecode.branch.BCIF_ICMPNE;
import bytecode.branch.BCJSR;
import bytecode.conversioninstruction.BCI2B;
import bytecode.conversioninstruction.BCI2C;

import bytecode.conversioninstruction.BCI2S;
import bytecode.loadstoreinstruction.BCACONST_NULL;
import bytecode.loadstoreinstruction.BCBIPUSH;
import bytecode.loadstoreinstruction.BCICONST;
import bytecode.loadstoreinstruction.BCIINC;
import bytecode.loadstoreinstruction.BCSIPUSH;
import bytecode.loadstoreinstruction.BCTypeLOAD;
import bytecode.loadstoreinstruction.BCTypeSTORE;
import bytecode.objectmanipulation.BCANEWARRAY;
import bytecode.objectmanipulation.BCARRAYLENGTH;
import bytecode.objectmanipulation.BCCHECKCAST;
import bytecode.objectmanipulation.BCINSTANCEOF;
import bytecode.objectmanipulation.BCGETFIELD;
import bytecode.objectmanipulation.BCGETSTATIC;
import bytecode.objectmanipulation.BCINVOKEINTERFACE;
import bytecode.objectmanipulation.BCINVOKESPECIAL;
import bytecode.objectmanipulation.BCINVOKESTATIC;
import bytecode.objectmanipulation.BCINVOKEVIRTUAL;
import bytecode.objectmanipulation.BCLDC;
import bytecode.objectmanipulation.BCLDC_W;
import bytecode.objectmanipulation.BCMULTIANEWARRAY;
import bytecode.objectmanipulation.BCNEW;
import bytecode.objectmanipulation.BCNEWARRAY;
import bytecode.objectmanipulation.BCPUTFIELD;
import bytecode.objectmanipulation.BCTypeALOAD;
import bytecode.objectmanipulation.BCTypeASTORE;
import bytecode.stackinstruction.BCDUP;
import bytecode.stackinstruction.BCDUP2;
import bytecode.stackinstruction.BCDUP2_X1;
import bytecode.stackinstruction.BCDUP2_X2;
import bytecode.stackinstruction.BCDUP_X1;
import bytecode.stackinstruction.BCDUP_X2;
import bytecode.stackinstruction.BCPOP;
import bytecode.stackinstruction.BCPOP2;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCMethod {
	private BCInstruction[] code;
	private Trace trace;
	//specification
	private ExsuresTable exsures;
	private Precondition precondition;
	private Postcondition postcondition;
	private AssertTable assertTable;
	
	
	private Expression[] modified;
	private BCLocalVariable[] localVariables;
	private BCConstantPool constantPool;
	//the constant pool added after to the class file ad an attribute
	private BCConstantPool secondConstantPool;
	
	
	private JavaType returnType;	
	private JavaType[] argTypes;
	
	private JavaObjectType[] exceptionsThrown;
	private BCExceptionTable exceptionTable;
	private Formula proofObligation;
	
	/**
	 * @param _mg
	 * @param _bcel_cp -
	 *            the representation of the constant pool in the bcel library.
	 *            Needed in the Method object to initialize certain data
	 *            structures
	 * @param _constantPool
	 */
	public BCMethod(MethodGen _mg, ConstantPoolGen _bcel_cp,
			BCConstantPool _constantPool) {
		
		//initiliasition
		setCode(code);
		setLocalVariables(_mg.getLocalVariables());
		setExceptionsThrown(_mg.getExceptions());
		constantPool = _constantPool;
		code = BCMethod.wrapByteCode(_mg.getInstructionList(), _mg, _bcel_cp,
				constantPool, localVariables);
		exceptionTable = new BCExceptionTable(_mg.getExceptionHandlers());
		//excHandlers = _mg.getExceptionHandlers();
		
		setAssertTable( );
		setPostcondition();
		setPrecondition();
		setExsures();
	}
	
	private void setAssertTable( ) {
		
	}
	private void setPostcondition( ) {
		
	}
	private void setPrecondition( ) {
		
	}
	
	private void setExsures( ) {
		
	}
	/**
	 * @param gens
	 */
	private void setLocalVariables(LocalVariableGen[] gens) {
		if (gens == null) {
			return;
		}
		if (gens.length <= 0) {
			return;
		}
		localVariables = new BCLocalVariable[gens.length];
		for (int i = 0; i < localVariables.length; i++) {
			localVariables[i] = new BCLocalVariable(gens[i]);
		}
	}
	/**
	 * get the local variable that is at index i
	 * 
	 * @param i -
	 *            index of the local variable
	 * @return local variable at index i
	 */
	public BCLocalVariable getLocalVariableAtIndex(int i) {
		return localVariables[i];
	}
	/**
	 * @return
	 */
	public BCInstruction[] getCode() {
		return code;
	}
	/**
	 * @return the exsures specification clause
	 */
	public ExsuresTable getExsures() {
		return exsures;
	}
	/**
	 * @return the predicate that must be true in the state after the execution
	 *         of the method
	 */
	public Formula getExsuresForException(JavaObjectType _exc_type) {
		return exsures.getExcPostconditionFor(_exc_type.getSignature());
	}
	/**
	 * @return the predicate that must be true in the state after the execution
	 *         of the method
	 */
	public Formula getPostcondition() {
		return postcondition.getPredicate();
	}
	/**
	 * @return the predicate that must be true in the state before the
	 *         execution of the method
	 */
	public Formula getPrecondition() {
		return precondition.getPredicate();
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
	 * @param trace
	 */
	private void setTrace(Trace trace) {
		this.trace = trace;
	}
	/**
	 * called by outside ? once the Method object is initialised
	 * 
	 * @param _mg
	 */
	protected void initTrace() {
		if (trace != null) {
			return;
		}
		setTrace(new Trace(code, getExceptionHandlers()));
	}
	
	
	public static BCInstruction[] wrapByteCode(InstructionList _il,
			MethodGen _mg, ConstantPoolGen _bcel_cp,
			BCConstantPool constantPool, BCLocalVariable[] _lv) {
		InstructionHandle[] _iharr = _il.getInstructionHandles();
		BCInstruction[] _bc = new BCInstruction[_iharr.length];
		Instruction instr;
		for (int i = 0; i < _iharr.length; i++) {
			instr = _iharr[i].getInstruction();
			Util.dump(" instruction type " + instr.getClass() );
			if (instr instanceof ReturnInstruction) {
				_bc[i] = new BCTypeRETURN(_iharr[i]);
			} else if (instr instanceof RET) {
				_bc[i] = new BCRET(_iharr[i]);
			} else if (instr instanceof GotoInstruction) {
				_bc[i] = new BCGOTO(_iharr[i]);
			} else if (instr instanceof ATHROW) {
				_bc[i] = new BCATHROW(_iharr[i]);
			} else if (instr instanceof JsrInstruction) {
				_bc[i] = new BCJSR(_iharr[i]);
			} else if (instr instanceof NOP) {
				_bc[i] = new BCNOP(_iharr[i]);
			} else if (instr instanceof IfInstruction) {
				if (instr instanceof IF_ACMPEQ) {
					_bc[i] = new BCIF_ACMPEQ(_iharr[i]);
				} else if (instr instanceof IF_ACMPNE) {
					_bc[i] = new BCIF_ACMPNE(_iharr[i]);
				} else if (instr instanceof IF_ICMPEQ) {
					_bc[i] = new BCIF_ICMPEQ(_iharr[i]);
				} else if (instr instanceof IF_ICMPGE) {
					_bc[i] = new BCIF_ICMPGE(_iharr[i]);
				} else if (instr instanceof IF_ICMPGT) {
					_bc[i] = new BCIF_ICMPGT(_iharr[i]);
				} else if (instr instanceof IF_ICMPLE) {
					_bc[i] = new BCIF_ICMPLE(_iharr[i]);
				} else if (instr instanceof IF_ICMPLT) {
					_bc[i] = new BCIF_ICMPLT(_iharr[i]);
				} else if (instr instanceof IF_ICMPNE) {
					_bc[i] = new BCIF_ICMPNE(_iharr[i]);
				} else if (_iharr[i].getInstruction() instanceof IFEQ) {
					_bc[i] = new BCIFEQ(_iharr[i]);
				} else if (instr instanceof IFGE) {
					_bc[i] = new BCIFGE(_iharr[i]);
				} else if (instr instanceof IFGT) {
					_bc[i] = new BCIFGT(_iharr[i]);
				} else if (instr instanceof IFLE) {
					_bc[i] = new BCIFLE(_iharr[i]);
				} else if (instr instanceof IFLT) {
					_bc[i] = new BCIFLT(_iharr[i]);
				} else if (instr instanceof IFNE) {
					_bc[i] = new BCIFNE(_iharr[i]);
				} else if (instr instanceof IFNONNULL) {
					_bc[i] = new BCIFNONNULL(_iharr[i]);
				} else if (instr instanceof IFNULL) {
					_bc[i] = new BCIFNULL(_iharr[i]);
				}
			} else if (instr instanceof ArithmeticInstruction) {
				//				JavaType _type =
				//					JavaType.getJavaRefType(
				//						((TypedInstruction) _iharr[i].getInstruction())
				//							.getType(_bcel_cp)
				//							.getSignature());
				//							
				if (instr instanceof IADD) {
					_bc[i] = new BCTypeADD(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof ISUB) {
					_bc[i] = new BCTypeSUB(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof IDIV) {
					_bc[i] = new BCTypeDIV(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof IREM) {
					_bc[i] = new BCTypeREM(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof INEG) {
					_bc[i] = new BCTypeNEG(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof IMUL) {
					_bc[i] = new BCTypeMUL(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof IAND) {
					_bc[i] = new BCTypeAND(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof IOR) {
					_bc[i] = new BCTypeOR(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof IXOR) {
					_bc[i] = new BCTypeXOR(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof ISHR) {
					_bc[i] = new BCTypeSHR(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof ISHL) {
					_bc[i] = new BCTypeSHL(_iharr[i], JavaType.JavaINT);
				} else if (instr instanceof IUSHR) {
					_bc[i] = new BCTypeUSHR(_iharr[i], JavaType.JavaINT);
				}
			} else if (instr instanceof ConversionInstruction) {
				if (instr instanceof I2B) {
					_bc[i] = new BCI2B(_iharr[i]);
				} else if (instr instanceof I2C) {
					_bc[i] = new BCI2C(_iharr[i]);
				} else if (instr instanceof I2S) {
					_bc[i] = new BCI2S(_iharr[i]);
				} else if (instr instanceof I2B) {
					_bc[i] = new BCI2B(_iharr[i]);
				}
			} else if (instr instanceof StackInstruction) {
				if (instr instanceof DUP_X1) {
					_bc[i] = new BCDUP_X1(_iharr[i]);
				} else if (instr instanceof DUP_X2) {
					_bc[i] = new BCDUP_X2(_iharr[i]);
				} else if (instr instanceof DUP) {
					_bc[i] = new BCDUP(_iharr[i]);
				} else if (instr instanceof DUP2) {
					_bc[i] = new BCDUP2(_iharr[i]);
				} else if (instr instanceof DUP2_X1) {
					_bc[i] = new BCDUP2_X1(_iharr[i]);
				} else if (instr instanceof DUP2_X2) {
					_bc[i] = new BCDUP2_X2(_iharr[i]);
				} else if (instr instanceof POP) {
					_bc[i] = new BCPOP(_iharr[i]);
				} else if (instr instanceof POP2) {
					_bc[i] = new BCPOP2(_iharr[i]);
				}
			} else if (instr instanceof ArrayInstruction) {
				JavaType _type = JavaType
						.getJavaRefType(((TypedInstruction) _iharr[i]
								.getInstruction()).getType(_bcel_cp)
								.getSignature());
				if ((instr instanceof AALOAD) || (instr instanceof BALOAD)
						|| (instr instanceof CALOAD)
						|| (instr instanceof LALOAD)
						|| (instr instanceof DALOAD)
						|| (instr instanceof FALOAD)
						|| (instr instanceof SALOAD)
						|| (instr instanceof IALOAD)) {
					_bc[i] = new BCTypeALOAD(_iharr[i], _type);
				}
				if ((instr instanceof AASTORE) || (instr instanceof BASTORE)
						|| (instr instanceof CASTORE)
						|| (instr instanceof LASTORE)
						|| (instr instanceof DASTORE)
						|| (instr instanceof FASTORE)
						|| (instr instanceof SASTORE)
						|| (instr instanceof IASTORE)) {
					_bc[i] = new BCTypeASTORE(_iharr[i], _type);
				}
				//cp instructions
			} else if (instr instanceof CPInstruction) {
				JavaType _type = JavaType
						.getJavaRefType(((TypedInstruction) instr).getType(
								_bcel_cp).getSignature());
				// the class where the field or method is declared
				JavaType _classType = null;
				if (instr instanceof FieldOrMethod) {
					_classType = JavaType
							.getJavaRefType(((FieldOrMethod) instr)
									.getClassType(_bcel_cp).getSignature());
				}
				if (instr instanceof InvokeInstruction) {
					if (instr instanceof INVOKEVIRTUAL) {
						_bc[i] = new BCINVOKEVIRTUAL(_iharr[i], _type,
								_classType, constantPool);
					} else if (instr instanceof INVOKESTATIC) {
						_bc[i] = new BCINVOKESTATIC(_iharr[i], _type,
								_classType, constantPool);
					} else if (instr instanceof INVOKESPECIAL) {
						_bc[i] = new BCINVOKESPECIAL(_iharr[i], _type,
								_classType, constantPool);
					} else if (instr instanceof INVOKEINTERFACE) {
						_bc[i] = new BCINVOKEINTERFACE(_iharr[i], _type,
								_classType, constantPool);
					}
					
				} else if (instr instanceof PUTFIELD) {
					_bc[i] = new BCPUTFIELD(_iharr[i], _type, _classType,
							constantPool);
				} else if (instr instanceof GETFIELD) {
					_bc[i] = new BCGETFIELD(_iharr[i], _type, _classType,
							constantPool);
				} else if (instr instanceof GETSTATIC) {
					_bc[i] = new BCGETSTATIC(_iharr[i], _type, _classType,
							constantPool);
				} else if (instr instanceof CHECKCAST) {
					_bc[i] = new BCCHECKCAST(_iharr[i], _type);
				} else if (instr instanceof LDC) {
					_bc[i] = new BCLDC(_iharr[i], _type, constantPool);
				} else if (instr instanceof LDC2_W) {
					_bc[i] = new BCLDC_W(_iharr[i], _type, constantPool);
				} else if (instr instanceof NEW) {
					_bc[i] = new BCNEW(_iharr[i], _type);
				} else if (instr instanceof ANEWARRAY) {
					_bc[i] = new BCANEWARRAY(_iharr[i], _type);
				} else if (instr instanceof MULTIANEWARRAY) {
					_bc[i] = new BCMULTIANEWARRAY(_iharr[i], _type);
				} else if (instr instanceof INSTANCEOF) {
					_bc[i] = new BCINSTANCEOF(_iharr[i], _type);
				} else if (instr instanceof NEWARRAY) {
					//					JavaType _type =
					//						JavaType.getJavaRefType(
					//							((TypedInstruction) instr)
					//								.getType(_bcel_cp)
					//								.getSignature());
					_bc[i] = new BCNEWARRAY(_iharr[i], _type);
				} 
			} else if (instr instanceof ARRAYLENGTH) {
				_bc[i] = new BCARRAYLENGTH(_iharr[i]);
			} else if (instr instanceof LocalVariableInstruction) {
				int localVarIndex = ((LocalVariableInstruction) instr)
						.getIndex();
				if (instr instanceof LoadInstruction) {
					_bc[i] = new BCTypeLOAD(_iharr[i], _lv[localVarIndex]);
				} else if (instr instanceof StoreInstruction) {
					_bc[i] = new BCTypeSTORE(_iharr[i], _lv[localVarIndex]);
				} else if (instr instanceof IINC) {
					_bc[i] = new BCIINC(_iharr[i], _lv[localVarIndex]);
				}
			} else if (instr instanceof PushInstruction) {
				if (instr instanceof ACONST_NULL) {
					_bc[i] = new BCACONST_NULL(_iharr[i]);
				} else if (instr instanceof BIPUSH) {
					_bc[i] = new BCBIPUSH(_iharr[i]);
				} else if (instr instanceof ICONST) {
					_bc[i] = new BCICONST(_iharr[i]);
				} else if (instr instanceof SIPUSH) {
					_bc[i] = new BCSIPUSH(_iharr[i]);
				}
			}
			_bc[i].setBCIndex(i);
			//set the bytecode command at the previous position and at the
			// next positition
			if (i > 0) {
				_bc[i].setPrev(_bc[i - 1]);
				_bc[i - 1].setNext(_bc[i]);
			}
		}
		_bc = Util.setTargets(_bc, _mg);
		return _bc;
	}
	/**
	 * @return
	 */
	public Expression[] getModified() {
		return modified;
	}
	public int getNumberArguments() {
		return 0;
	}
	public JavaType getReturnType() {
		return returnType;
	}
	
	/**
	 * @return
	 */
	public JavaObjectType[] getExceptionsThrown() {
		return exceptionsThrown;
	}
	
	public void wp() {
		if (trace == null){
			return ;
		}
		Formula  f = trace.wp();
		f = new Formula( precondition.getPredicate(), f, Connector.IMPLIES) ;
	}
	/**
	 * @param exceptionsThrown The exceptionsThrown to set.
	 */
	public void setExceptionsThrown(String[] _exc ) {
		exceptionsThrown = new JavaObjectType[_exc.length];
		for (int i = 0; i <  _exc.length; i++) {
			exceptionsThrown[i] = (JavaObjectType) JavaType.getJavaRefType( _exc[i]);
		}
	}
	
	public ExceptionHandler[] getExceptionHandlers() {
			return exceptionTable.getExcHandlers();
	}
}
