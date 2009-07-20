/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package test;

import java.util.Vector;

import org.apache.bcel.generic.ARRAYLENGTH;
import org.apache.bcel.generic.ArithmeticInstruction;
import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConversionInstruction;
import org.apache.bcel.generic.DUP_X1;
import org.apache.bcel.generic.DUP_X2;
import org.apache.bcel.generic.I2B;
import org.apache.bcel.generic.I2C;
import org.apache.bcel.generic.I2S;
import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.IF_ACMPEQ;
import org.apache.bcel.generic.IF_ACMPNE;
import org.apache.bcel.generic.INVOKEINTERFACE;
import org.apache.bcel.generic.ISUB;
import org.apache.bcel.generic.IfInstruction;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.LoadInstruction;
import org.apache.bcel.generic.LocalVariableInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.StackInstruction;
import org.apache.bcel.generic.StoreInstruction;
import org.apache.bcel.generic.TypedInstruction;

import utils.Util;
import bcclass.BCClass;
import bcclass.BCConstantPool;
import bcclass.attributes.AssertTable;
import bcclass.attributes.BCExceptionHandlerTable;
import bcclass.attributes.BCLineNumber;
import bcclass.attributes.BlockSpecification;
import bcclass.attributes.LoopSpecification;
import bcclass.attributes.MethodSpecification;
import bcexpression.BCLocalVariable;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bytecode.BCInstruction;
import bytecode.BCTypeRETURN;
import bytecode.arithmetic.BCTypeADD;
import bytecode.arithmetic.BCTypeSUB;
import bytecode.block.Trace;
import bytecode.branch.BCIF_ACMPEQ;
import bytecode.branch.BCIF_ACMPNE;
import bytecode.conversioninstruction.BCI2B;
import bytecode.conversioninstruction.BCI2C;
import bytecode.conversioninstruction.BCI2S;
import bytecode.loadstoreinstruction.BCTypeLOAD;
import bytecode.loadstoreinstruction.BCTypeSTORE;
import bytecode.objectmanipulation.BCARRAYLENGTH;
import bytecode.objectmanipulation.BCINVOKEINTERFACE;
import bytecode.objectmanipulation.BCNEWARRAY;
import bytecode.stackinstruction.BCDUP_X1;
import bytecode.stackinstruction.BCDUP_X2;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCMethod {

	private BCInstruction[] bytecode;
	private Trace trace;
	private String name;
	
	
	//specification
	private AssertTable assertTable;
	private LoopSpecification loopSpecification;
	private BlockSpecification blockSpecification;
	private MethodSpecification methodSpecification;

	private Vector proofObligation;

	private BCLineNumber[] lineNumberTable;
	private BCLocalVariable[] localVariables;

	private String signature;
	private String[] argNames;

	private JavaType returnType;
	private JavaType[] argTypes;
	private JavaObjectType[] exceptionsThrown;
	private BCExceptionHandlerTable exceptionHandlerTable;
	
	private BCClass  clazz;
	private boolean initialised = false;
	
	private MethodGen bcelMethod;

	public static BCInstruction[] wrapByteCode(
		MethodGen _mg,
		BCConstantPool constantPool,
		BCLocalVariable[] _lv) {
		ConstantPoolGen _bcel_cp = _mg.getConstantPool();
		InstructionList _il = _mg.getInstructionList();
		if (_il == null) {
			return null;
		}
		InstructionHandle[] _iharr = _il.getInstructionHandles();
		BCInstruction[] _bc = new BCInstruction[_iharr.length];
		Instruction instr;
		try {
			//		Util.dump( " ****************** wrapByteCode ************* " );
			for (int i = 0; i < _iharr.length; i++) {
				instr = _iharr[i].getInstruction();

				if (instr instanceof ReturnInstruction) {
					_bc[i] = new BCTypeRETURN(_iharr[i]);
				} else if (instr instanceof IfInstruction) {
					if (instr instanceof IF_ACMPEQ) {
						_bc[i] = new BCIF_ACMPEQ(_iharr[i]);
					} else if (instr instanceof IF_ACMPNE) {
						_bc[i] = new BCIF_ACMPNE(_iharr[i]);
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
					}
				} else if (instr instanceof StackInstruction) {
					if (instr instanceof DUP_X1) {
						_bc[i] = new BCDUP_X1(_iharr[i]);
					} else if (instr instanceof DUP_X2) {
						_bc[i] = new BCDUP_X2(_iharr[i]);
					} 
				} else if (instr instanceof CPInstruction) {
					JavaType _type =
						JavaType.getJavaRefType(
							((TypedInstruction) instr)
								.getType(_bcel_cp)
								.getSignature());
					// the class where the field or method is declared
					JavaType _classType = null;
					if (instr instanceof INVOKEINTERFACE) {
							_bc[i] =
								new BCINVOKEINTERFACE(
									_iharr[i],
									_type,
									_classType,
									constantPool);
						}

					} else if (instr instanceof NEWARRAY) {
					JavaType _type =
						JavaType.getJavaRefType(
							((NEWARRAY) instr).getType().getSignature());
					_bc[i] = new BCNEWARRAY(_iharr[i], _type);
				} else if (instr instanceof LocalVariableInstruction) {
					int localVarIndex =
						((LocalVariableInstruction) instr).getIndex();
					if (instr instanceof LoadInstruction) {
						_bc[i] = new BCTypeLOAD(_iharr[i], _lv[localVarIndex]);
					}  
				} 
				_bc[i].setBytecode(_bc);
				_bc[i].setBCIndex(i);
			
				//				Util.dump(_bc[i].toString());
				//set the bytecode command at the previous position and at the
				// next positition
				if (i > 0) {
					_bc[i].setPrev(_bc[i - 1]);
					_bc[i - 1].setNext(_bc[i]);
					//					Util.dump(" ::::: prev  : " + _bc[i - 1]);

				}
			}
			_bc = Util.setTargets(_bc);
		} catch (Exception e) {
			e.printStackTrace();
		}

		return _bc;
	}
	
/*	*//**
	 * @return
	 *//*
	public ModifiesExpression[] getModifies() {
		if (methodSpecification == null) {
			return null;
		}
		SpecificationCase[] specCases =
			methodSpecification.getSpecificationCases();
		return specCases[0].getModifies();
	}*/



}

