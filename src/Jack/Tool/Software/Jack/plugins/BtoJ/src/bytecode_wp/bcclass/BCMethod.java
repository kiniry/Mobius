/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcclass;

import jack.util.Logger;

import java.util.Collection;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.LineNumber;
import org.apache.bcel.classfile.LineNumberTable;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.*;

import bytecode_to_JPO.B2JPackage;
import bytecode_wp.bc.io.AttributeReader;
import bytecode_wp.bc.io.ReadAttributeException;
import bytecode_wp.bcclass.attributes.Assert;
import bytecode_wp.bcclass.attributes.AssertTable;
import bytecode_wp.bcclass.attributes.BCAttribute;
import bytecode_wp.bcclass.attributes.BCExceptionHandlerTable;
import bytecode_wp.bcclass.attributes.BCLineNumber;
import bytecode_wp.bcclass.attributes.BlockSpecification;
import bytecode_wp.bcclass.attributes.ClassInvariant;
import bytecode_wp.bcclass.attributes.ExceptionHandler;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcclass.attributes.LoopSpecification;
import bytecode_wp.bcclass.attributes.MethodSpecification;
import bytecode_wp.bcclass.attributes.ModifiesSet;
import bytecode_wp.bcclass.attributes.Postcondition;
import bytecode_wp.bcclass.attributes.SETTable;
import bytecode_wp.bcclass.attributes.SingleLoopSpecification;
import bytecode_wp.bcclass.attributes.SpecificationCase;
import bytecode_wp.bcclass.utils.MethodSignature;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.ValueAtState;
import bytecode_wp.bcexpression.javatype.JavaArrType;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.OLD;
import bytecode_wp.bcexpression.jml.RESULT;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCATHROW;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCLoopEnd;
import bytecode_wp.bytecode.BCLoopStart;
import bytecode_wp.bytecode.BCNOP;
import bytecode_wp.bytecode.BCRET;
import bytecode_wp.bytecode.BCTypeRETURN;
import bytecode_wp.bytecode.EntryPoint;
import bytecode_wp.bytecode.arithmetic.BCTypeADD;
import bytecode_wp.bytecode.arithmetic.BCTypeAND;
import bytecode_wp.bytecode.arithmetic.BCTypeDIV;
import bytecode_wp.bytecode.arithmetic.BCTypeMUL;
import bytecode_wp.bytecode.arithmetic.BCTypeNEG;
import bytecode_wp.bytecode.arithmetic.BCTypeOR;
import bytecode_wp.bytecode.arithmetic.BCTypeREM;
import bytecode_wp.bytecode.arithmetic.BCTypeSHL;
import bytecode_wp.bytecode.arithmetic.BCTypeSHR;
import bytecode_wp.bytecode.arithmetic.BCTypeSUB;
import bytecode_wp.bytecode.arithmetic.BCTypeUSHR;
import bytecode_wp.bytecode.arithmetic.BCTypeXOR;
import bytecode_wp.bytecode.block.ControlFlowGraph;
import bytecode_wp.bytecode.block.IllegalLoopException;
import bytecode_wp.bytecode.branch.BCGOTO;
import bytecode_wp.bytecode.branch.BCIFEQ;
import bytecode_wp.bytecode.branch.BCIFGE;
import bytecode_wp.bytecode.branch.BCIFGT;
import bytecode_wp.bytecode.branch.BCIFLE;
import bytecode_wp.bytecode.branch.BCIFLT;
import bytecode_wp.bytecode.branch.BCIFNE;
import bytecode_wp.bytecode.branch.BCIFNONNULL;
import bytecode_wp.bytecode.branch.BCIFNULL;
import bytecode_wp.bytecode.branch.BCIF_ACMPEQ;
import bytecode_wp.bytecode.branch.BCIF_ACMPNE;
import bytecode_wp.bytecode.branch.BCIF_ICMPEQ;
import bytecode_wp.bytecode.branch.BCIF_ICMPGE;
import bytecode_wp.bytecode.branch.BCIF_ICMPGT;
import bytecode_wp.bytecode.branch.BCIF_ICMPLE;
import bytecode_wp.bytecode.branch.BCIF_ICMPLT;
import bytecode_wp.bytecode.branch.BCIF_ICMPNE;
import bytecode_wp.bytecode.branch.BCJSR;
import bytecode_wp.bytecode.conversioninstruction.BCI2B;
import bytecode_wp.bytecode.conversioninstruction.BCI2C;
import bytecode_wp.bytecode.conversioninstruction.BCI2L;
import bytecode_wp.bytecode.conversioninstruction.BCI2S;
import bytecode_wp.bytecode.conversioninstruction.BCL2I;
import bytecode_wp.bytecode.loadstoreinstruction.BCACONST_NULL;
import bytecode_wp.bytecode.loadstoreinstruction.BCBIPUSH;
import bytecode_wp.bytecode.loadstoreinstruction.BCIINC;
import bytecode_wp.bytecode.loadstoreinstruction.BCSIPUSH;
import bytecode_wp.bytecode.loadstoreinstruction.BCTypeCONST;
import bytecode_wp.bytecode.loadstoreinstruction.BCTypeLOAD;
import bytecode_wp.bytecode.loadstoreinstruction.BCTypeSTORE;
import bytecode_wp.bytecode.objectmanipulation.BCANEWARRAY;
import bytecode_wp.bytecode.objectmanipulation.BCARRAYLENGTH;
import bytecode_wp.bytecode.objectmanipulation.BCCHECKCAST;
import bytecode_wp.bytecode.objectmanipulation.BCGETFIELD;
import bytecode_wp.bytecode.objectmanipulation.BCGETSTATIC;
import bytecode_wp.bytecode.objectmanipulation.BCINSTANCEOF;
import bytecode_wp.bytecode.objectmanipulation.BCINVOKEINTERFACE;
import bytecode_wp.bytecode.objectmanipulation.BCINVOKESPECIAL;
import bytecode_wp.bytecode.objectmanipulation.BCINVOKESTATIC;
import bytecode_wp.bytecode.objectmanipulation.BCINVOKEVIRTUAL;
import bytecode_wp.bytecode.objectmanipulation.BCInvoke;
import bytecode_wp.bytecode.objectmanipulation.BCLDC;
import bytecode_wp.bytecode.objectmanipulation.BCLDC_W;
import bytecode_wp.bytecode.objectmanipulation.BCMULTIANEWARRAY;
import bytecode_wp.bytecode.objectmanipulation.BCNEW;
import bytecode_wp.bytecode.objectmanipulation.BCNEWARRAY;
import bytecode_wp.bytecode.objectmanipulation.BCPUTFIELD;
import bytecode_wp.bytecode.objectmanipulation.BCPUTSTATIC;
import bytecode_wp.bytecode.objectmanipulation.BCTypeALOAD;
import bytecode_wp.bytecode.objectmanipulation.BCTypeASTORE;
import bytecode_wp.bytecode.stackinstruction.BCDUP;
import bytecode_wp.bytecode.stackinstruction.BCDUP2;
import bytecode_wp.bytecode.stackinstruction.BCDUP2_X1;
import bytecode_wp.bytecode.stackinstruction.BCDUP2_X2;
import bytecode_wp.bytecode.stackinstruction.BCDUP_X1;
import bytecode_wp.bytecode.stackinstruction.BCDUP_X2;
import bytecode_wp.bytecode.stackinstruction.BCPOP;
import bytecode_wp.bytecode.stackinstruction.BCPOP2;
import bytecode_wp.constants.MemUsedConstant;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.memory.allocation.MethodAllocation;
import bytecode_wp.memory.allocation1.CalculateMeth;
import bytecode_wp.memory.allocation1.CalculateMethFrwrd;
import bytecode_wp.modifexpression.ModifiesExpression;
import bytecode_wp.modifexpression.ModifiesIdent;
import bytecode_wp.utils.Util;
import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCMethod extends AccessFlags {
	public static final String INIT = "<init>";

	private BCInstruction[] bytecode;

	private ControlFlowGraph trace;

	private String name;

	// specification
	private AssertTable assertTable;

	private SETTable setTable;

	private LoopSpecification loopSpecification;

	private BlockSpecification blockSpecification;

	private MethodSpecification methodSpecification;

	private Vector proofObligation;

	private BCLineNumber[] lineNumberTable;

	private RegisterTable localVariables;

	private String signature;

	private String[] argNames;

	private JavaType returnType;

	private JavaType[] argTypes;

	private JavaObjectType[] exceptionsThrown;

	private BCExceptionHandlerTable exceptionHandlerTable;

	// the class where this method is declared
	private BCClass clazz;

	// a flag that indicates if the control flow graph is intialized or not
	private boolean initialised = false;

	private MethodGen bcelMethod;

	/**
	 * @param _mg
	 * @param _bcel_cp -
	 *            the representation of the constant pool in the bcel library.
	 *            Needed in the Method object to initialize certain data
	 *            structures
	 * @param _constantPool
	 */
	public BCMethod(MethodGen _mg, BCClass _class, ConstantPoolGen cpGen)
			throws ReadAttributeException {
		super(_mg.getAccessFlags());
		clazz = _class;
		name = _mg.getName();
		setLocalVariables(_mg, cpGen);
		setExceptionsThrown(_mg.getExceptions());

		setArgNames(_mg.getArgumentNames());
		setArgumentTypes(_mg.getArgumentTypes());
		setReturnType(_mg.getReturnType());
		bcelMethod = _mg;

		// Util.dump(
		// "init method delcared in class: "
		// + _mg.getClassName()
		// + " | methodName: "
		// + _mg.getName()
		// + " ---");
		// Util.dump(" method signature " + signature);

	}

	public BCLocalVariable[] getLocalVariables() {
		if (localVariables == null)
			return new BCLocalVariable[0];
		else
			return localVariables.getLocalVariables();
	}

	public boolean isInit() {
		if (name.equals(INIT)) {
			return true;
		}
		return false;
	}

	// called from outside when the method should be initialised
	public void initMethod() throws ReadAttributeException,
			IllegalLoopException {

		if (initialised) {
			return;
		}
		signature = MethodSignature
				.getSignature(getArgTypes(), getReturnType());
		bytecode = BCMethod.wrapByteCode(bcelMethod, this, clazz
				.getConstantPool(), localVariables);
		exceptionHandlerTable = new BCExceptionHandlerTable(bcelMethod
				.getExceptionHandlers());
		setLineNumbers(bcelMethod.getLineNumberTable(bcelMethod
				.getConstantPool()));
		setAttributes(bcelMethod.getAttributes());
		initTrace();// find loop entries
		if (MEMCHECK) {
			initMethCons(); // infer an upper bound for the memory used by the
							// method
		}
		setAsserts();
		setInvariantToHoldAtMethCall();
		setInvariantInMethodSpecification();
		setLoopInvariants();
		initialised = true;
	}

	private void setInvariantInMethodSpecification() {
		if (methodSpecification == null) {
			return;
		}
		methodSpecification.setInvariant(clazz.getClassInvariant());
		Formula historyConstraints = clazz.getHistoryConstraints();
		methodSpecification.setHistoryConstraint(historyConstraints);
	}

	private void setLineNumbers(LineNumberTable _lineNumberTable) {
		LineNumber[] lineNumbers = _lineNumberTable.getLineNumberTable();
		if (lineNumbers == null) {
			return;
		}
		if (lineNumbers.length == 0) {
			return;
		}
		this.lineNumberTable = new BCLineNumber[lineNumbers.length];
		for (int i = 0; i < lineNumbers.length; i++) {
			lineNumberTable[i] = new BCLineNumber(lineNumbers[i].getStartPC(),
					lineNumbers[i].getLineNumber());
		}
	}

	/**
	 * called in BCClass.initMethods(Method[] _methods, ConstantPoolGen cp) sets
	 * the assertions if there are any
	 */
	public void setAsserts() {
		if (assertTable == null) {
			return;
		}
		Assert[] asserts = assertTable.getAsserts();
		if (asserts == null) {
			return;
		}
		for (int i = 0; i < asserts.length; i++) {
			int pos = asserts[i].getPosition();
			Formula assertion = asserts[i].getPredicate();
			BCInstruction instr = Util
					.getBCInstructionAtPosition(bytecode, pos);
			instr.setAssert(assertion);
		}
	}

	public void setInvariantToHoldAtMethCall() {
		ClassInvariant inv = clazz.getClassInvariant();
		if (inv == null) {
			return;
		}
		Formula invariant = inv.getClassInvariant();
		if (bytecode == null) {
			return;
		}
		for (int i = 0; i < bytecode.length; i++) {
			if (bytecode[i] instanceof BCInvoke) {
				bytecode[i].setAssert((Formula) invariant.copy());
			}
		}
	}

	/**
	 * called in BCClass.initMethods(Method[] _methods, ConstantPoolGen cp) sets
	 * the assertions if there are any
	 */
	public void setAssignToModel() {
		/*
		 * if (assertTable == null) { return; } Assert[] asserts =
		 * assertTable.getAsserts(); if (asserts == null) { return; } for (int i =
		 * 0; i < asserts.length; i++) { int pos = asserts[i].getPosition();
		 * Formula assertion = asserts[i].getPredicate(); BCInstruction instr =
		 * Util.getBCInstructionAtPosition(bytecode, pos);
		 * instr.setAssert(assertion); }
		 */
	}

	/*
	 * public Formula getStateVectorAtInstr(int state) { Formula fieldsAtInstr =
	 * (Formula)clazz.getVectorAtState(state); Formula localVarsAtInstr =
	 * (Formula)getLocalVariableStateAtInstr(state); Formula f =
	 * Formula.getFormula(fieldsAtInstr, localVarsAtInstr, Connector.AND);
	 * return f; }
	 * 
	 * public Formula getVectorAtStateToHold(IJml2bConfiguration config, int
	 * state, ModifiesSet modifies) { Formula fieldsAtInstr = (Formula)
	 * clazz.getModifiesCondition(config, state, modifies, null); Formula
	 * localVarsAtInstr = getLocalVariableAtStateToHold(state, modifies);
	 * Formula modifiesAtState = modifies.getPostcondition(config, state);
	 * Formula f = Formula.getFormula(fieldsAtInstr, localVarsAtInstr,
	 * Connector.AND); f = Formula.getFormula(f, modifiesAtState,
	 * Connector.AND); return f; }
	 */
	/**
	 * generates the following assertion :
	 * 
	 * forall i : 0 <= i < locVar.length. loc(i) == loc(i)^atState(instr)
	 * 
	 * @param state
	 * @return
	 */
	public Formula getLocalVariableAtStateToHold(int state, ModifiesSet modifies) {
		Formula localVarsAtInstr = Predicate0Ar.TRUE;
		if (localVariables == null) {
			return localVarsAtInstr;
		}
		for (int i = 1; i < localVariables.getLength(); i++) {
			if (modifies.modifies(localVariables.getLocalVariableAtIndex(i))) {
				continue;
			}
			Expression localVarAtInstr = new ValueAtState(localVariables
					.getLocalVariableAtIndex(i), state);
			Predicate localVarAtInstrEqLocVar = new Predicate2Ar(localVariables
					.getLocalVariableAtIndex(i), localVarAtInstr,
					PredicateSymbol.EQ);
			localVarsAtInstr = Formula.getFormula(localVarsAtInstr,
					localVarAtInstrEqLocVar, Connector.AND);
		}
		return localVarsAtInstr;
	}

	public Formula getLocalVarAtStateToAssume(int state, ModifiesSet modifies) {
		Formula localVarsAtInstr = Predicate0Ar.TRUE;
		if (localVariables == null) {
			return localVarsAtInstr;
		}
		for (int i = 1; i < localVariables.getLength(); i++) {
			if (!modifies.modifies(localVariables.getLocalVariableAtIndex(i))) {
				continue;
			}
			Expression localVarAtInstr = new ValueAtState(localVariables
					.getLocalVariableAtIndex(i), state);
			Predicate localVarAtInstrEqLocVar = new Predicate2Ar(localVariables
					.getLocalVariableAtIndex(i), localVarAtInstr,
					PredicateSymbol.EQ);
			localVarsAtInstr = Formula.getFormula(localVarsAtInstr,
					localVarAtInstrEqLocVar, Connector.AND);
		}
		return localVarsAtInstr;
	}

	private BCLoopStart getLoopStartNearTo(int pos) {
		BCInstruction loop = Util.getBCInstructionAtPosition(bytecode, pos);
		if (loop instanceof BCLoopStart) {
			return (BCLoopStart) loop;
		}
		while (!(loop instanceof BCLoopStart)) {
			if (loop instanceof EntryPoint) {
				loop = ((EntryPoint) loop).getWrappedInstruction();
				// if the entrypoint is actually a loop entry
				if (loop instanceof BCLoopStart) {
					return (BCLoopStart) loop;
				}

			}
			if (loop instanceof BCGOTO) {
				loop = ((BCGOTO) loop).getTarget();
			} else if (loop instanceof BCLoopEnd) {
				int loopEntryPos = ((BCLoopEnd) loop).getLoopEntry();
				loop = Util.getBCInstructionAtPosition(bytecode, loopEntryPos);
			} else {
				loop = loop.getNext();
			}
		}
		return (BCLoopStart) loop;

	}

	/**
	 * 
	 * called in BCClass.initMethods(Method[] _methods, ConstantPoolGen cp) sets
	 * the invariants for the loops in the bytecode of the method if there are
	 * any
	 * 
	 * this method is called once the exec graph of the method is created
	 */
	public void setLoopInvariants() {
		if (loopSpecification == null) {
			return;
		}
		SingleLoopSpecification[] loops = loopSpecification
				.getLoopSpecifications();
		if (loops == null) {
			return;
		}
		for (int i = 0; i < loops.length; i++) {
			SingleLoopSpecification loopSpec = loops[i];
			int posLoopEntry = loopSpec.getLoopIndex();
			// Formula loopInvariant = loopSpec.getInvariant();
			// Expression decreases = loopSpec.getDecreases();
			BCLoopStart loopStart = getLoopStartNearTo(posLoopEntry);

			/* BCLoopStart loopStart = trace.getLoopWithIndex( loopIndex); */
			loopStart.setInvariant(loopSpec.getInvariant());
			loopStart.setDecreases(loopSpec.getDecreases());
			loopStart.setMethod(this);

			loopStart.setModifies(loopSpec.getModifies());
			Vector loopEnds = loopStart.getLoopEndPositions();
			for (int k = 0; k < loopEnds.size(); k++) {
				int loopEndPos = ((Integer) loopEnds.elementAt(k)).intValue();
				BCLoopEnd loopEnd = (BCLoopEnd) Util
						.getBCInstructionAtPosition(bytecode, loopEndPos);
				loopEnd.setInvariant(loopSpec.getInvariant());
				loopEnd.setDecreases(loopSpec.getDecreases());
				loopEnd.setMethod(this);
				loopEnd.setModifies(loopSpec.getModifies());
			}
		}
	}

	private void setAttributes(Attribute[] _attributes)
			throws ReadAttributeException {
		Unknown privateAttr = null;

		for (int i = 0; i < _attributes.length; i++) {
			if (_attributes[i] instanceof Unknown) {
				privateAttr = (Unknown) _attributes[i];
				BCAttribute bcAttribute = null;

				if (localVariables != null) {
					bcAttribute = AttributeReader.readAttribute(privateAttr,
							clazz, lineNumberTable, localVariables
									.getLocalVariables());
				} else {
					bcAttribute = AttributeReader.readAttribute(privateAttr,
							clazz, lineNumberTable, null);
				}
				if (bcAttribute instanceof MethodSpecification) {
					methodSpecification = (MethodSpecification) bcAttribute;
					Formula resultBoolConstraints = generateBoolExpressionConditions();
					if (resultBoolConstraints != Predicate0Ar.TRUE) {
						methodSpecification
								.setReturnBoolConstraints(resultBoolConstraints);
					}
				} else if (bcAttribute instanceof AssertTable) {
					assertTable = (AssertTable) bcAttribute;
				} else if (bcAttribute instanceof SETTable) {
					setTable = (SETTable) bcAttribute;
				} else if (bcAttribute instanceof LoopSpecification) {
					loopSpecification = (LoopSpecification) bcAttribute;
				} else if (bcAttribute instanceof BlockSpecification) {
					blockSpecification = (BlockSpecification) bcAttribute;
				}
			}
		}

	}

	/**
	 * @param type
	 */
	private void setReturnType(Type _type) {
		returnType = JavaType.getJavaType(_type);
	}

	/**
	 * @param types
	 */
	private void setArgumentTypes(Type[] _types) {
		if (_types == null) {
			return;
		}
		if (_types.length == 0) {
			return;
		}
		argTypes = new JavaType[_types.length];
		for (int i = 0; i < _types.length; i++) {
			JavaType type = JavaType.getJavaType(_types[i]);
			argTypes[i] = type;
		}
	}

	/**
	 * @param exceptionsThrown
	 *            The exceptionsThrown to set.
	 */
	public void setExceptionsThrown(String[] _exc) {
		exceptionsThrown = new JavaObjectType[_exc.length];
		for (int i = 0; i < _exc.length; i++) {
			exceptionsThrown[i] = (JavaObjectType) JavaType
					.getJavaRefType(_exc[i]);
		}
	}

	/**
	 * this method sets the local variables of a method
	 * 
	 * @param
	 */
	private void setLocalVariables(MethodGen m, ConstantPoolGen cpGen) {
		LocalVariableGen[] locVarTable = m.getLocalVariables();
		if ((locVarTable == null) || (locVarTable.length <= 0)) {

			if ((bcelMethod != null) && (bcelMethod.isAbstract())) {
				String[] names = bcelMethod.getArgumentNames();
				Type[] types = bcelMethod.getArgumentTypes();
				localVariables = new RegisterTable();
				for (int i = 0; i < names.length; i++) {
					JavaType type = JavaType.getJavaType(types[i]);
					BCLocalVariable lv = new BCLocalVariable(names[i], i, type,
							this);
					localVariables.addRegister(lv);
				}
			}
			return;
		}

		localVariables = new RegisterTable();

		for (int i = 0; i < locVarTable.length; i++) {
			JavaType type = JavaType.getJavaType(locVarTable[i].getType());
			int indLV = locVarTable[i].getIndex();
			if (localVariables.searchForDuplicate(indLV)) {
				continue;
			}
			BCLocalVariable lv = new BCLocalVariable(locVarTable[i]
					.getLocalVariable(cpGen), type, this);

			localVariables.addRegister(lv);
		}
	}

	/**
	 * 
	 * //modified the search of the variable at index : because of the
	 * realisation of bcel : if there is a local variable coded with two bytes
	 * the local variable array is diminuished with 1
	 * 
	 * get the local variable that is at index i
	 * 
	 * @param i -
	 *            index of the local variable
	 * @return local variable at index i
	 */
	public BCLocalVariable getLocalVariableAtIndex(int i) {
		// // commented because of the bcel realisation
		// //return localVariables[i]
		// int bcelIndex = i;
		// for (int s= 0; s<= i;s++) {
		// if (localVariables[i].getLength() == 2 ) {
		// bcelIndex = bcelIndex - 1;
		// }
		// }
		if (localVariables == null) {
			return null;
		}

		return localVariables.getLocalVariableAtIndex(i);
	}

	/**
	 * @return
	 */
	public BCInstruction[] getCode() {
		return bytecode;
	}

	/**
	 * @return the predicate that must be true in the state after the execution
	 *         of the method
	 */
	public VCGPath getExsuresForException(JavaObjectType _exc_type) {
		if (methodSpecification == null) {
			return VCGPath.initVCwithGoalFalse();
		}
		SpecificationCase[] specCases = methodSpecification
				.getSpecificationCases();
		ExsuresTable exsures = specCases[0].getExsures();
		if (exsures == null) {
			return VCGPath.initVCwithGoalFalse();
		}
		VCGPath vcg = new VCGPath();
		exsures.getExsPostconditionThrow(_exc_type.getSignature(), vcg);
		return vcg;
	}

	/**
	 * @return the predicate that must be true in the state after the execution
	 *         of the method . This method is called when the corresponding
	 *         method is called
	 */
	public Formula getExsuresForExceptionOnCall(JavaObjectType _exc_type) {
		if (methodSpecification == null) {
			return Predicate0Ar.FALSE;
		}
		SpecificationCase[] specCases = methodSpecification
				.getSpecificationCases();
		ExsuresTable exsures = specCases[0].getExsures();
		if (exsures == null) {
			return Predicate0Ar.FALSE;
		}
		return exsures.getExsPostconditionThrow(_exc_type.getSignature());
	}

	/**
	 * @return the predicate that must be true in the state after the execution
	 *         of the method
	 */
	/*
	 * public Formula getPostcondition() { if (methodSpecification == null) {
	 * return Predicate.TRUE; } SpecificationCase[] specCases =
	 * methodSpecification.getSpecificationCases(); return
	 * specCases[0].getPostcondition(); }
	 */
	/*	*//**
			 * @return the predicate that must be true in the state before the
			 *         execution of the method
			 */
	/*
	 * public Formula getPrecondition() { if (methodSpecification == null) {
	 * return Predicate.TRUE; } SpecificationCase[] specCases =
	 * methodSpecification.getSpecificationCases(); return
	 * specCases[0].getPrecondition(); }
	 */
	/**
	 * @return
	 */
	public ControlFlowGraph getTrace() {
		return trace;
	}

	/**
	 * @param trace
	 */
	private void setTrace(ControlFlowGraph trace) {
		this.trace = trace;
	}

	/**
	 * called by outside ? once the Method object is initialised
	 * 
	 * @param _mg
	 * @throws IllegalLoopException
	 */
	protected void initTrace() throws IllegalLoopException {
		if (trace != null) {
			return;
		}
		setTrace(new ControlFlowGraph(this));
	}

	public static BCInstruction[] wrapByteCode(MethodGen _mg, BCMethod meth,
			BCConstantPool constantPool, RegisterTable _lv) {
		ConstantPoolGen _bcel_cp = _mg.getConstantPool();
		InstructionList _il = _mg.getInstructionList();
		if (_il == null) {
			return null;
		}
		InstructionHandle[] _iharr = _il.getInstructionHandles();
		BCInstruction[] _bc = new BCInstruction[_iharr.length];
		Instruction instr;
		try {
			// Util.dump( " ****************** wrapByteCode ************* " );
			for (int i = 0; i < _iharr.length; i++) {
				instr = _iharr[i].getInstruction();

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
					// JavaType _type =
					// JavaType.getJavaRefType(
					// ((TypedInstruction) _iharr[i].getInstruction())
					// .getType(_bcel_cp)
					// .getSignature());
					//							
					if (instr instanceof IADD) {
						_bc[i] = new BCTypeADD(_iharr[i], JavaType.JavaINT);
					} else if (instr instanceof ISUB) {
						_bc[i] = new BCTypeSUB(_iharr[i], JavaType.JavaINT);
					} else if (instr instanceof LSUB) {
						_bc[i] = new BCTypeSUB(_iharr[i], JavaType.JavaLONG);
					} else if (instr instanceof IDIV) {
						_bc[i] = new BCTypeDIV(_iharr[i], JavaType.JavaINT);
					} else if (instr instanceof LDIV) {
						_bc[i] = new BCTypeDIV(_iharr[i], JavaType.JavaLONG);
					} else if (instr instanceof IREM) {
						_bc[i] = new BCTypeREM(_iharr[i], JavaType.JavaINT);

					} else if (instr instanceof LREM) {
						_bc[i] = new BCTypeREM(_iharr[i], JavaType.JavaLONG);
					} else if (instr instanceof INEG) {
						_bc[i] = new BCTypeNEG(_iharr[i], JavaType.JavaINT);
					} else if (instr instanceof LNEG) {
						_bc[i] = new BCTypeNEG(_iharr[i], JavaType.JavaLONG);
					} else if (instr instanceof IMUL) {
						_bc[i] = new BCTypeMUL(_iharr[i], JavaType.JavaINT);
					} else if (instr instanceof LMUL) {
						_bc[i] = new BCTypeMUL(_iharr[i], JavaType.JavaLONG);
					} else if (instr instanceof IAND) {
						_bc[i] = new BCTypeAND(_iharr[i], JavaType.JavaINT);
					} else if (instr instanceof LAND) {
						_bc[i] = new BCTypeAND(_iharr[i], JavaType.JavaINT);
					} else if (instr instanceof IOR) {
						_bc[i] = new BCTypeOR(_iharr[i], JavaType.JavaINT);
					} else if (instr instanceof LOR) {
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
					} else if (instr instanceof I2L) {
						_bc[i] = new BCI2L(_iharr[i]);
					} else if (instr instanceof L2I) {
						_bc[i] = new BCL2I(_iharr[i]);
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
					if ((instr instanceof AASTORE)
							|| (instr instanceof BASTORE)
							|| (instr instanceof CASTORE)
							|| (instr instanceof LASTORE)
							|| (instr instanceof DASTORE)
							|| (instr instanceof FASTORE)
							|| (instr instanceof SASTORE)
							|| (instr instanceof IASTORE)) {
						_bc[i] = new BCTypeASTORE(_iharr[i], _type);
					}
					// cp instructions
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
					} else if (instr instanceof PUTSTATIC) {
						_bc[i] = new BCPUTSTATIC(_iharr[i], _type, _classType,
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
						JavaArrType arrType = JavaType
								.getJavaArrTypeWithBasicType(_type);
						_bc[i] = new BCANEWARRAY(_iharr[i], arrType);
					} else if (instr instanceof MULTIANEWARRAY) {
						_bc[i] = new BCMULTIANEWARRAY(_iharr[i], _type);
					} else if (instr instanceof INSTANCEOF) {
						_bc[i] = new BCINSTANCEOF(_iharr[i], _type);
					}
				} else if (instr instanceof NEWARRAY) {
					JavaType _type = JavaType.getJavaRefType(((NEWARRAY) instr)
							.getType().getSignature());
					_bc[i] = new BCNEWARRAY(_iharr[i], _type);
				} else if (instr instanceof ARRAYLENGTH) {
					_bc[i] = new BCARRAYLENGTH(_iharr[i]);
				} else if (instr instanceof LocalVariableInstruction) {
					int localVarIndex = ((LocalVariableInstruction) instr)
							.getIndex();
					BCLocalVariable locVar = null;
					if (_lv != null) {
						locVar = _lv.getLocalVariableAtIndex(localVarIndex);
					}
					if (locVar == null) {
						locVar = new BCLocalVariable(localVarIndex, meth);
					}
					if (instr instanceof LoadInstruction) {
						_bc[i] = new BCTypeLOAD(_iharr[i], locVar);
					} else if (instr instanceof StoreInstruction) {
						_bc[i] = new BCTypeSTORE(_iharr[i], locVar);
					} else if (instr instanceof IINC) {
						_bc[i] = new BCIINC(_iharr[i], locVar);
					}
				} else if (instr instanceof PushInstruction) {
					if (instr instanceof ACONST_NULL) {
						_bc[i] = new BCACONST_NULL(_iharr[i]);
					} else if (instr instanceof BIPUSH) {
						_bc[i] = new BCBIPUSH(_iharr[i]);
					} else if (instr instanceof ICONST) {
						_bc[i] = new BCTypeCONST(_iharr[i], JavaType.JavaINT);
					} else if (instr instanceof LCONST) {
						_bc[i] = new BCTypeCONST(_iharr[i], JavaType.JavaLONG);
					} else if (instr instanceof SIPUSH) {
						_bc[i] = new BCSIPUSH(_iharr[i]);
					}
				}
				if (_bc[i] == null) {
					// TODO must be changed - when there is unrecognized
					// instruction
					// ane exception must be thrown
					return null;
				}
				_bc[i].setBytecode(_bc);
				_bc[i].setBCIndex(i);

				// Util.dump(_bc[i].toString());
				// set the bytecode command at the previous position and at the
				// next positition
				if (i > 0) {
					_bc[i].setPrev(_bc[i - 1]);
					_bc[i - 1].setNext(_bc[i]);
					// Util.dump(" ::::: prev : " + _bc[i - 1]);

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
			 */
	/*
	 * public ModifiesExpression[] getModifies() { if (methodSpecification ==
	 * null) { return null; } SpecificationCase[] specCases =
	 * methodSpecification.getSpecificationCases(); return
	 * specCases[0].getModifies(); }
	 */
	public int getNumberArguments() {
		return argNames.length;
	}

	public JavaType getReturnType() {
		if (returnType == JavaType.JavaBOOLEAN) {
			return JavaType.JavaINT;
		}
		return returnType;
	}

	/**
	 * @return
	 */
	public JavaObjectType[] getExceptionsThrown() {
		return exceptionsThrown;
	}

	public void setInitPOG() {
		initProofObligation();
		proofObligation.add(Predicate0Ar.TRUE);
	}

	/**
	 * converts the verification conditions from the internal form to formulas
	 * 
	 */
	private void addToProveObligations() {
		Vector v = trace.getWP();

		initProofObligation();
		if (v == null) {
			return;
		}

		if (v == null) {
			return;
		}
		for (int j = 0; j < v.size(); j++) {
			VCGPath vcg = (VCGPath) v.elementAt(j);
			vcg = (VCGPath) vcg.removeOLD();
			vcg = (VCGPath) vcg.simplify();
			/*
			 * for (int i = 0; i < vcg.getNumVc(); i++) { Formula f =
			 * vcg.getProveObligationAt(i); Vector goals = vcg.getGoalsAt( i );
			 * f = (Formula) f.removeOLD(); f = (Formula) f.simplify(); if (f ==
			 * Predicate0Ar.TRUE) continue; proofObligation.add(f); }
			 */
		}
		proofObligation.addAll(v);
	}

	private void initProofObligation() {
		if (proofObligation == null) {
			proofObligation = new Vector();
		}
	}

	public void wp(IJml2bConfiguration config) {
		Util.dump("wp for method " + getName());
		if (trace == null) {
			return;
		}
		VCGPath vcg = new VCGPath();
		SpecificationCase[] specCases = null;
		Formula historyConstraints = null;
		if (methodSpecification == null) {
			vcg.addGoal(VcType.NORM_POST, Predicate0Ar.TRUE);
			addClassInvariantsToProve(config, vcg);
			trace.wp(config, vcg, null);
			addInitMethHypothesis();
			addToProveObligations();
		} else {
			specCases = methodSpecification.getSpecificationCases();
			historyConstraints = clazz.getHistoryConstraints();
			if (isInit()) {
				vcg.addGoal(VcType.INSTANCE_INVARIANT, methodSpecification
						.getInvariantAfterInit());
			} else {
				vcg.addGoal(VcType.INSTANCE_INVARIANT, methodSpecification
						.getInvariant());
			}
		}
		if (historyConstraints != null) {
			vcg.addGoal(VcType.HISTORY_CONSTR, historyConstraints);
		}
		if (specCases == null) {
			addClassInvariantsToProve(config, vcg);
			trace.wp(config, vcg, null);
			addInitMethHypothesis();
			addToProveObligations();
			Util.dump(clazz.getName() + " " + getName() + " " + getSignature());
			Util.dump(proofObligation);
			Logger.get().println(
					getName() + " < num POgs " + proofObligation.size() + ">");
			return;
		}

		for (int i = 0; i < specCases.length; i++) {
			VCGPath specCasevcg = (VCGPath) vcg.copy();
			clazz.getModifiesCondition(config, ClassStateVector.RETURN_STATE,
					specCases[i].getModifies(), specCasevcg);
			// specCasevcg.addGoal(VcType.MODIFIES, modifCondition );
			addClassInvariantsToProve(config, vcg);
			/*
			 * Formula postSpecCase =
			 * specCases[i].getPostconditionToProve(specCasevcg);
			 */
			/* specCasevcg.addGoal(VcType.NORM_POST_SPEC_CASE, postSpecCase ); */
			specCases[i].getPostconditionToProve(specCasevcg);
			/*
			 * Formula f = generateBoolExpressionConditions();
			 * specCasevcg.addGoal(VcType.RESULT_IS_BOOLEAN,f);
			 */
			setReturnHyp(specCasevcg);
			trace.wp(config, specCasevcg, specCases[i].getExsures());

		}
		if (getName().equals("setData")) {
			Util.dump("here");
		}
		addInitMethHypothesis();
		addToProveObligations();
		initWp();

		Util.dump(clazz.getName() + " " + getName() + " " + getSignature());
		Util.dump(proofObligation);
		Util.out.println(getName() + " < num POgs " + proofObligation.size()
				+ ">");
		System.gc();

	}

	/**
	 * sets the hypothesis that the return result is 0 or 1 if the return type
	 * is boolean This is because the JVM does not support boolean types
	 * 
	 * 
	 * @param vcg -
	 *            add the hypothesis for the return value if necessary
	 */
	private void setReturnHyp(VCGPath vcg) {
		if (returnType != JavaType.JavaBOOLEAN) {
			return;
		}
		Predicate res_Eq_1 = new Predicate2Ar(new Stack(Expression.COUNTER),
				new NumberLiteral(1), PredicateSymbol.EQ);
		Predicate res_Eq_0 = new Predicate2Ar(new Stack(Expression.COUNTER),
				new NumberLiteral(0), PredicateSymbol.EQ);
		Formula res_is_0_or_1 = Formula.getFormula(res_Eq_0, res_Eq_1,
				Connector.OR);
		Integer key = vcg.addHyp(0, res_is_0_or_1);
		vcg.addHypsToVCs(key);
	}

	private void addInitMethHypothesis() {

		Vector v = trace.getWP();
		if (v == null) {
			return;
		}
		for (int j = 0; j < v.size(); j++) {
			VCGPath wp = (VCGPath) v.elementAt(j);

			if (methodSpecification != null) {
				Integer key1 = wp.addHyp(0, methodSpecification.getInvariant());
				wp.addHypsToVCs(key1);
				Formula desugaredPre = methodSpecification
						.getDesugaredPrecondition();
				Integer key2 = wp.addHyp(0, desugaredPre);
				wp.addHypsToVCs(key2);
			}
			wp.generateBoolConstraints();
			if (!isStatic()) {
				// hypothesis that this is not null
				Formula this_neq_null = new Predicate2Ar(
						getLocalVariableAtIndex(0), Expression._NULL,
						PredicateSymbol.EQ);
				this_neq_null = Formula
						.getFormula(this_neq_null, Connector.NOT);
				Integer key4 = wp.addHyp(0, this_neq_null);
				wp.addHypsToVCs(key4);
			}
			for (int k = 0; k < localVariables.getLength(); k++) {
				if ( getLocalVariableAtIndex(k)
						.getType() == JavaType.JavaINT) {
					continue;
				}
				if ( getLocalVariableAtIndex(k)
						.getType() == JavaType.JavaINT) {
					continue;
				}
				if ( getLocalVariableAtIndex(k)
						.getType() == JavaType.JavaCHAR) {
					continue;
				}
				Predicate this_subType_ = new Predicate2Ar(new TYPEOF(
						getLocalVariableAtIndex(k)), getLocalVariableAtIndex(k)
						.getType(), PredicateSymbol.SUBTYPE);
				Integer key5 = wp.addHyp(0, this_subType_);
				wp.addHypsToVCs(key5);
			}

			/* Logger.get().println(wp); */
		}
	}

	/**
	 * reinitiliases to nul all the wps stored in the entrypoint instructions
	 */
	private void initWp() {
		trace.initWp();
	}


/*	public BCMethod getSuperMethod (IJml2bConfiguration config) {
		BCClass superCl = clazz.getSuperClass(config);
		
		Collection ms = superCl.getMethods();
		Iterator it = ms.iterator() ;
		while (it.hasNext()) {
			
			BCMethod m = (BCMethod)it.next();
			JavaType retT = m.getReturnType();
			if (JavaType. returnType )
			JavaType[] types =  m.getArgTypes();
		}
	} */
	
	/**
	 * generates verification for behavioral subtyping - postcondition case
	 */		
	Formula behaveSubtypePost(BCMethod mS) {
		MethodSpecification methodSpecification = mS.getMethodSpecification();
		SpecificationCase[] specCasesSuper = methodSpecification
				.getSpecificationCases();
		Formula postSuper = specCasesSuper[0].getPostcondition();

		postSuper = (Formula) postSuper.atState(0);
		postSuper = (Formula)postSuper.removeOLD();
		// ///////////////////
		SpecificationCase[] specCasesSub = methodSpecification
				.getSpecificationCases();
		Formula postSub = specCasesSub[0].getPostcondition();
		postSub = (Formula) postSub.atState(0);
		postSub = (Formula)postSub.removeOLD();
		
		Formula cond = Formula.getFormula(postSub,
				new Predicate2Ar(new BCLocalVariable(0), Expression._NULL,
						PredicateSymbol.NOTEQ), Connector.AND);
		
		for (int k = 0; k < localVariables.getLength(); k++) {
			Predicate this_subType_ = new Predicate2Ar(new TYPEOF(
					getLocalVariableAtIndex(k)), getLocalVariableAtIndex(k)
					.getType(), PredicateSymbol.SUBTYPE);
			cond = Formula.getFormula(cond, this_subType_ , Connector.AND);
		}
		
		cond = Formula.getFormula(cond, postSuper, Connector.IMPLIES );
		
		return cond;
	}

	/*
	 * private void setWP(Formula precondition ) { Vector v = trace.getWP(); if
	 * (proofObligation == null) { proofObligation = new Vector(); } Formula
	 * invariant = clazz.getClassInvariant(); for (int i = 0; i < v.size();i++) {
	 * Formula wp = (Formula)v.elementAt(i); wp =
	 * Formula.getFormula(precondition, wp, Connector.IMPLIES ); // if not a
	 * constructor then then the invariant should hold in the prestate of method
	 * execution if (getName() != BCMethod.INIT) { wp = Formula.getFormula( wp ,
	 * invariant, Connector.AND ); } proofObligation.add(wp); } }
	 */

	public ExceptionHandler[] getExceptionHandlers() {
		return exceptionHandlerTable.getExcHandlers();
	}

	/**
	 * Returns the name.
	 * 
	 * @return String
	 */
	public String getName() {
		return name;
	}

	/**
	 * Sets the name.
	 * 
	 * @param name
	 *            The name to set
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * Returns the signature.
	 * 
	 * @return String
	 */
	public String getSignature() {
		// signature = MethodSignature.getSignature(getArgTypes() ,
		// getReturnType() );
		return signature;
	}

	/**
	 * Returns the argNames.
	 * 
	 * @return String[]
	 */
	public String[] getArgNames() {
		return argNames;
	}

	/**
	 * Sets the argNames.
	 * 
	 * @param argNames
	 *            The argNames to set
	 */
	public void setArgNames(String[] argNames) {
		this.argNames = argNames;
	}

	/**
	 * Returns the bytecode.
	 * 
	 * @return BCInstruction[]
	 */
	public BCInstruction[] getBytecode() {
		return bytecode;
	}

	public String toString() {
		return clazz.getName() + "." + name + "" + signature;
	}

	/**
	 * @return Returns the methodSpecification.
	 */
	public MethodSpecification getMethodSpecification() {
		return methodSpecification;
	}

	/**
	 * @return Returns the proofObligation.
	 */
	public Vector getProofObligation() {
		return proofObligation;
	}

	/**
	 * @return Returns the argTypes.
	 */
	public JavaType[] getArgTypes() {
		return argTypes;
	}

	// /////////////////////////////////////////
	// /////////////////////////////////////////
	// ///Memory ALlocation//////////////////
	// //////////////////////////////////////
	// /////////////////////////////////////
	private boolean checked = false;

	public void setChecked(boolean _checked) {
		checked = _checked;
	}

	public boolean isChecked() {

		return checked;
	}

	private int allocations;

	/**
	 * @return Returns the allocations.
	 */
	public int getAllocations() {
		return allocations;
	}

	/**
	 * @param allocations
	 *            The allocations to set.
	 */
	public void setAllocations(int _allocations) {
		this.allocations = _allocations;
	}

	/**
	 * @return Returns the clazz
	 */
	public BCClass getClazz() {
		return clazz;
	}

	// ////////////////////////////////////////////////////////////
	// /////////////////////////////////////////////////////////////
	// //////////////Memory constraint consumption specification/////
	// //////////////////////////////////////////////////////////////
	// /////////////////////////////////////////////////////////////
	int memUsed = -1;

	public static boolean MEMCHECK = false;

	private void initMethCons() {
		memUsed = CalculateMethFrwrd.memConsMeth(bytecode);
		System.out.println(getSignature() + " : MEMUSED = " + memUsed);
	}

	public void initMethodSpecForMemoryConsumption() {
		// requires MemUsed + alloc <= Max
		FieldAccess memUsed = new FieldAccess(MemUsedConstant.MemUsedCONSTANT);
		Expression upperBoundForConsum = new NumberLiteral(allocations);
		Expression memUsed_pluc_upperBound = ArithmeticExpression
				.getArithmeticExpression(memUsed, upperBoundForConsum,
						ExpressionConstants.ADD);
		Formula requiresFormula = new Predicate2Ar(memUsed_pluc_upperBound,
				MethodAllocation.MAX, PredicateSymbol.LESSEQ);

		// ensures MemUsed <= old(MemUsed) + alloc
		Expression oldMemUsed_plus_upperBound = ArithmeticExpression
				.getArithmeticExpression(new OLD(memUsed), upperBoundForConsum,
						ExpressionConstants.ADD);
		Formula ensuresFormula = new Predicate2Ar(memUsed.copy(),
				oldMemUsed_plus_upperBound, PredicateSymbol.LESSEQ);

		// modifies MemUsed
		/* ModifiesSet modifies = null; */
		ModifiesExpression modExpr = new ModifiesIdent(new FieldAccess(
				MemUsedConstant.MemUsedCONSTANT), clazz);
		ModifiesSet modifSet = new ModifiesSet(
				new ModifiesExpression[] { modExpr }, clazz);

		// set the specification generated for every method
		SpecificationCase specCase = new SpecificationCase(requiresFormula,
				new Postcondition(ensuresFormula), modifSet, null);
		methodSpecification = new MethodSpecification(Predicate0Ar.TRUE,
				new SpecificationCase[] { specCase });
	}

	/**
	 * generates constraints for the return value if its actual type is bool. As
	 * the VM does provide a poor support for boolean type, the bools are
	 * represented as int but whose value is 0 or 1
	 * 
	 * @return
	 */
	public Formula generateBoolExpressionConditions() {
		if (returnType == JavaType.JavaBOOLEAN) {
			Predicate2Ar c0 = new Predicate2Ar(RESULT._RESULT,
					new NumberLiteral(0), PredicateSymbol.EQ);
			Predicate2Ar c1 = new Predicate2Ar(RESULT._RESULT,
					new NumberLiteral(1), PredicateSymbol.EQ);
			Formula f = Formula.getFormula(c0, c1, Connector.OR);
			return f;
		}
		return Predicate0Ar.TRUE;
	}

	void addClassInvariantsToProve(IJml2bConfiguration config, VCGPath path) {
		Enumeration classes = ((B2JPackage) config.getPackage()).getClasses()
				.elements();
		if (classes == null) {
			return;
		}
		while (classes.hasMoreElements()) {
			BCClass cl = (BCClass) classes.nextElement();
			ClassInvariant inv = cl.getClassInvariant();
			if (inv == null) {
				continue;
			}

			path.addGoal(VcType.INSTANCE_INVARIANT, inv.getClassInvariant());
		}
	}
}
