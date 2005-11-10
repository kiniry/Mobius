/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

import java.util.Vector;

import memory.allocation.MethodAllocation;
import modifexpression.Everything;
import modifexpression.ModifiesExpression;
import modifexpression.ModifiesIdent;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.LineNumber;
import org.apache.bcel.classfile.LineNumberTable;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.LocalVariableTable;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.*;

import constants.BCConstantFieldRef;
import constants.MemUsedConstant;

import utils.Util;
import bc.io.AttributeReader;
import bc.io.ReadAttributeException;
import bcclass.attributes.Assert;
import bcclass.attributes.AssertTable;
import bcclass.attributes.BCAttribute;
import bcclass.attributes.BCExceptionHandlerTable;
import bcclass.attributes.BCLineNumber;
import bcclass.attributes.BlockSpecification;
import bcclass.attributes.ExceptionHandler;
import bcclass.attributes.ExsuresTable;
import bcclass.attributes.LoopSpecification;
import bcclass.attributes.MethodSpecification;
import bcclass.attributes.ModifiesSet;
import bcclass.attributes.SingleLoopSpecification;
import bcclass.attributes.SpecificationCase;
import bcclass.utils.MethodSignature;
import bcexpression.ArithmeticExpression;
import bcexpression.BCLocalVariable;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.FieldAccess;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaArrType;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.OLD;
import bcexpression.jml.OLD_LOOP;
import bytecode.BCATHROW;
import bytecode.BCInstruction;
import bytecode.BCLoopEnd;
import bytecode.BCLoopStart;
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
import bytecode.block.IllegalLoopException;
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
import bytecode.objectmanipulation.BCGETFIELD;
import bytecode.objectmanipulation.BCGETSTATIC;
import bytecode.objectmanipulation.BCINSTANCEOF;
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
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;
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
	private RegisterTable localVariables;

	private String signature;
	private String[] argNames;

	private JavaType returnType;
	private JavaType[] argTypes;
	private JavaObjectType[] exceptionsThrown;
	private BCExceptionHandlerTable exceptionHandlerTable;
	
	private BCClass  clazz;
	
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
		clazz = _class;
		setLocalVariables(_mg, cpGen);
		setExceptionsThrown(_mg.getExceptions());
		name = _mg.getName();
		setArgNames(_mg.getArgumentNames());
		setArgumentTypes(_mg.getArgumentTypes());
		setReturnType(_mg.getReturnType());
		bcelMethod = _mg;
		
//		Util.dump(
//			"init method  delcared in class:  "
//				+ _mg.getClassName()
//				+ " | methodName:  "
//				+ _mg.getName()
//				+ "   ---");
//		Util.dump(" method signature " + signature);

	}
	
	public BCLocalVariable[] getLocalVariables() {
		return localVariables.getLocalVariables();
	}
	
	
	// called from outside when the method should be initialised
	public void initMethod() throws ReadAttributeException, IllegalLoopException {
		if (initialised) {
			return;
		}
		signature =  MethodSignature.getSignature(getArgTypes() , getReturnType() );
//		Util.dump("initMethod  " +clazz.getName() + "."+  getName() + " " + getSignature() );
		bytecode =
			BCMethod.wrapByteCode(bcelMethod, this, clazz.getConstantPool(), localVariables);
		exceptionHandlerTable =
			new BCExceptionHandlerTable(bcelMethod.getExceptionHandlers());
		setLineNumbers(
			bcelMethod.getLineNumberTable(bcelMethod.getConstantPool()));
		setAttributes(bcelMethod.getAttributes());
/*		if(methodSpecification != null) {
			methodSpecification.setInvariant(clazz.getClassInvariant());
			methodSpecification.setHistoryConstraint(clazz.getHistoryConstraints() );
		}*/
		/*setSpecification();*/
		initTrace();
		setAsserts();
		setLoopInvariants();
		
		initialised = true;
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
			lineNumberTable[i] =
				new BCLineNumber(
					lineNumbers[i].getStartPC(),
					lineNumbers[i].getLineNumber());
		}
	}
	/**
	 * called in BCClass.initMethods(Method[] _methods, ConstantPoolGen cp)
	 * sets the assertions if there are any
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
			BCInstruction instr =
				Util.getBCInstructionAtPosition(bytecode, pos);
			instr.setAssert(assertion);
		}
	}
	
	
	/**
	 * called in BCClass.initMethods(Method[] _methods, ConstantPoolGen cp)
	 * sets the assertions if there are any
	 */
	public void setAssignToModel() {
		/*if (assertTable == null) {
			return;
		}
		Assert[] asserts = assertTable.getAsserts();
		if (asserts == null) {
			return;
		}
		for (int i = 0; i < asserts.length; i++) {
			int pos = asserts[i].getPosition();
			Formula assertion = asserts[i].getPredicate();
			BCInstruction instr =
				Util.getBCInstructionAtPosition(bytecode, pos);
			instr.setAssert(assertion);
		}*/
	}
/*	public Formula getStateVectorAtInstr(int state) {
			Formula fieldsAtInstr = (Formula)clazz.getVectorAtState(state);
			Formula localVarsAtInstr = (Formula)getLocalVariableStateAtInstr(state);
			Formula  f = Formula.getFormula(fieldsAtInstr, localVarsAtInstr, Connector.AND);
			return f;
	}*/
	public Formula getVectorAtStateToHold(int state, ModifiesSet modifies) {
		Formula fieldsAtInstr = (Formula)clazz.getVectorAtStateToHold(state, modifies);
		Formula localVarsAtInstr = getLocalVariableAtStateToHold(state, modifies);
		Formula modifiesAtState = modifies.getPostcondition(state);
		Formula  f = Formula.getFormula(fieldsAtInstr, localVarsAtInstr, Connector.AND);
		f = Formula.getFormula(f, modifiesAtState, Connector.AND );
		return f;
	}

	/**
	 * generates the following assertion :
	 * 
	 * forall i : 0 <= i < locVar.length. loc(i) == loc(i)^atState(instr)
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
			Expression localVarAtInstr = localVariables.getLocalVariableAtIndex(i).atState(state);
			Predicate localVarAtInstrEqLocVar = new Predicate2Ar(localVariables.getLocalVariableAtIndex(i), localVarAtInstr, PredicateSymbol.EQ );
			localVarsAtInstr = Formula.getFormula(localVarsAtInstr, localVarAtInstrEqLocVar, Connector.AND );
		}		
		return localVarsAtInstr;
	}
	
	public Formula  getLocalVarAtStateToAssume(int state, ModifiesSet modifies) {
		Formula localVarsAtInstr = Predicate0Ar.TRUE;
		if (localVariables == null) {
			return localVarsAtInstr;
		}
		for (int i = 1; i < localVariables.getLength(); i++) {
			if (!modifies.modifies(localVariables.getLocalVariableAtIndex(i))) {
				continue;
			}
			Expression localVarAtInstr = localVariables.getLocalVariableAtIndex(i).atState(state);
			Predicate localVarAtInstrEqLocVar = new Predicate2Ar(localVariables.getLocalVariableAtIndex(i), localVarAtInstr, PredicateSymbol.EQ );
			localVarsAtInstr = Formula.getFormula(localVarsAtInstr, localVarAtInstrEqLocVar, Connector.AND );
		}		
		return localVarsAtInstr;
	}
	
	/**
	 * 
	 * called in BCClass.initMethods(Method[] _methods, ConstantPoolGen cp)
	 * sets the invariants for the loops 
	 * in the bytecode of the method if there are any 
	 * 
		 * this method is called once the exec graph of the method is created 
	 */
	public void setLoopInvariants() {
		if (loopSpecification == null) {
			return;
		}
		SingleLoopSpecification[] loops =
			loopSpecification.getLoopSpecifications();
		if (loops == null) {
			return;
		}
		for (int i = 0; i < loops.length; i++) {
			SingleLoopSpecification loopSpec = loops[i];
			int pos = loopSpec.getCpIndex();
			Formula loopInvariant = loopSpec.getInvariant();
			Expression decreases = loopSpec.getDecreases();
			BCLoopStart loopStart =
				(BCLoopStart) Util.getBCInstructionAtPosition(bytecode, pos +3 );
			loopStart.setInvariant(loopInvariant);
			loopStart.setDecreases( decreases);
			loopStart.setMethod(this);
			/* in the loop start no need to know the decreases formula .Needed only in the end of the loop */
			//			loopStart.setDecreases(decreases);
			loopStart.setModifies(loopSpec.getModifies());
			Vector loopEnds = loopStart.getLoopEndPositions();
			for (int k = 0; k < loopEnds.size(); k++) {
				int loopEndPos = ((Integer) loopEnds.elementAt(k)).intValue();
				BCLoopEnd loopEnd =
					(BCLoopEnd) Util.getBCInstructionAtPosition(
						bytecode,
						loopEndPos);
				loopEnd.setInvariant(loopInvariant);
				loopEnd.setDecreases(decreases);
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
				BCAttribute bcAttribute =
					AttributeReader.readAttribute(
						privateAttr,
						clazz.getConstantPool(),
						lineNumberTable, 
						localVariables.getLocalVariables());
				if (bcAttribute instanceof MethodSpecification) {
					methodSpecification = (MethodSpecification) bcAttribute;
					
				} else if (bcAttribute instanceof AssertTable) {
					assertTable = (AssertTable) bcAttribute;
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
	 * @param exceptionsThrown The exceptionsThrown to set.
	 */
	public void setExceptionsThrown(String[] _exc) {
		exceptionsThrown = new JavaObjectType[_exc.length];
		for (int i = 0; i < _exc.length; i++) {
			exceptionsThrown[i] =
				(JavaObjectType) JavaType.getJavaRefType(_exc[i]);
		}
	}

	private void setSpecification() {
		Util.dump("setSpecification for method  " + name);
		if (name.equals("wrapByteCode")) {
			SingleLoopSpecification loopSpec =
				new SingleLoopSpecification(489, new ModifiesSet(new ModifiesExpression[]{null}, clazz.getConstantPool()), Predicate0Ar.TRUE, null);
			SingleLoopSpecification[] loopSpecs =
				new SingleLoopSpecification[] { loopSpec };
			loopSpecification = new LoopSpecification(loopSpecs);
		}
		SpecificationCase specCase =
			new SpecificationCase(
				Predicate0Ar.TRUE,
				Predicate0Ar.TRUE,
				new ModifiesSet(new ModifiesExpression[]{Everything.EVERYTHING}, clazz.getConstantPool()),
				null);
		methodSpecification =
			new MethodSpecification(
				Predicate0Ar.TRUE,
				new SpecificationCase[] { specCase });
		/*BCConstantPool constantPool = clazz.getConstantPool();
		if (name.equals("half")) {

			//////////////////////////////////////////////////////////////////////////////////////////////////////////
			// POSTCONDITION = f1 /\ f2 //////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

			// f1 : old( loc(0) ) div 2 == loc(1)
			Predicate2Ar loc1_eq_loc0Div2 =
				new Predicate2Ar(
					ArithmeticExpression.getArithmeticExpression(
						new OLD(new LocalVariable(1)),
						new NumberLiteral(2),
						ExpressionConstants.DIV),
					new LocalVariable(2),
					PredicateSymbol.EQ);

			// f2	: even( loc(0) ) 		
			Predicate1Ar loc_0_even =
				new Predicate1Ar(
					new LocalVariable(1),
					PredicateSymbol.EVEN);

			Formula postcondition =
				Formula.getFormula(loc1_eq_loc0Div2, loc_0_even, Connector.AND);

			///////////////////////////////////////////////////////////////////////////////////
			////////////PRECONDITION 
			//loc(0)>=0
			Predicate2Ar precondition =
				new Predicate2Ar(
					new LocalVariable(1),
					new NumberLiteral(0),
					PredicateSymbol.GRTEQ);

			//			MODIFIES
			ModifiesIdent modif_loc1 = new ModifiesIdent( new LocalVariable(1), clazz.getConstantPool() );
			ModifiesIdent modif_loc2 = new ModifiesIdent( new LocalVariable(2), clazz.getConstantPool() );
			ModifiesExpression[] modifies = new ModifiesExpression[] { modif_loc1, modif_loc2 };

			SpecificationCase specCase =
				new SpecificationCase(
					precondition,
					postcondition,
					new ModifiesSet(modifies),
					null);
			//LOOP SPEC
			// old(n) == n + a*2; 
			methodSpecification =
				new MethodSpecification(
					Predicate.TRUE,
					new SpecificationCase[] { specCase });

			ArithmeticExpression loc1_mult_2 =
				(
					ArithmeticExpression) ArithmeticExpression
						.getArithmeticExpression(
					new LocalVariable(2),
					new NumberLiteral(2),
					ExpressionConstants.MULT);
			ArithmeticExpression loc1_mult_2_plus_loc0 =
				(
					ArithmeticExpression) ArithmeticExpression
						.getArithmeticExpression(
					loc1_mult_2,
					new LocalVariable(1),
					ExpressionConstants.ADD);

			//LOOP INVARIANT
			Predicate invariant =
				new Predicate2Ar(
					new OLD(new LocalVariable(1)),
					loc1_mult_2_plus_loc0,
					PredicateSymbol.EQ);

			Expression[] loopModif =
				new Expression[] { modif_loc1, modif_loc2 };

			SingleLoopSpecification loopSpec =
				new SingleLoopSpecification(11, new ModifiesSet(loopModif), invariant, null);
			SingleLoopSpecification[] loopSpecs =
				new SingleLoopSpecification[] { loopSpec };
			loopSpecification = new LoopSpecification(loopSpecs);

		}
		if (name.equals("testMethodInvokation")) {
			Predicate2Ar postcondition =
				new Predicate2Ar(
					Expression._RESULT,
					Expression._NULL,
					PredicateSymbol.NOTEQ);
			Predicate0Ar precondition = Predicate.TRUE;

			SpecificationCase specCase =
				new SpecificationCase(precondition, postcondition, null, null);
			methodSpecification =
				new MethodSpecification(
					Predicate.TRUE,
					new SpecificationCase[] { specCase });
		}

		if (name.equals("testThisAccess")) {
			//postcondition
			Predicate2Ar postcondition =
				new Predicate2Ar(
					Expression._RESULT,
					localVariables[0],
					PredicateSymbol.EQ);
			//precondition
			Predicate0Ar precondition = Predicate.TRUE;
			// modifies
			ModifiesExpression[] modifies =
				new ModifiesExpression[] { new ModifiesArray( new ModifiesDOT(new ModifiesIdent( constantPool.getConstant(15), constantPool), localVariables[0] ,constantPool ), new ArrayElemFromTo(new NumberLiteral(1), new NumberLiteral(5) ),constantPool )};
			// exsures 
			
			Expression arrayLength =
				new FieldAccess(
					ArrayLengthConstant.ARRAYLENGTHCONSTANT,
					new FieldAccess(
						(BCConstantFieldRef) constantPool.getConstant(15),
						localVariables[0]));
			Formula exsPost =
				new Predicate2Ar(
					arrayLength,
					new NumberLiteral(2),
					PredicateSymbol.LESS);
			// this.arr.length < 2	
			Exsures exsures =
				new Exsures(
					exsPost,
					(JavaObjectType) JavaType.getJavaType(
						ClassNames.ARRAYINDEXOUTOFBOUNDException));
			ExsuresTable exsTable = new ExsuresTable(new Exsures[] { exsures });
			SpecificationCase specCase =
				new SpecificationCase(
					precondition,
					postcondition,
					new ModifiesSet(modifies, clazz.getConstantPool()),
					exsTable);
			methodSpecification =
				new MethodSpecification(
					Predicate.TRUE,
					new SpecificationCase[] { specCase });

		}

		if (name.equals("mod")) {
			//METHOD SPEC
			//postcondition :  \result ==\old(  loc(1) ) mod loc(2)
			ArithmeticExpression mod =
				(
					ArithmeticExpression) ArithmeticExpression
						.getArithmeticExpression(
					new LocalVariable(1),
					new LocalVariable(2),
					ExpressionConstants.REM);
			Predicate2Ar postcondition =
				new Predicate2Ar(Expression._RESULT, mod, PredicateSymbol.EQ);
			// precondition : TRUE
			Predicate0Ar precondition = Predicate.TRUE;

			// modifies loc(1)
			ModifiesIdent modif_loc1 = new ModifiesIdent( new LocalVariable(1), constantPool  );
			ModifiesIdent modif_loc4 = new ModifiesIdent ( new LocalVariable(4), constantPool );

			ModifiesExpression[] modifies = new ModifiesExpression[] { modif_loc1, modif_loc4 };
			SpecificationCase specCase =
				new SpecificationCase(
					precondition,
					postcondition,
					new ModifiesSet(modifies),
					null);
			methodSpecification =
				new MethodSpecification(
					Predicate.TRUE,
					new SpecificationCase[] { specCase });

			// LOOP SPEC
			ArithmeticExpression loc_4_mult_loc_2 =
				(
					ArithmeticExpression) ArithmeticExpression
						.getArithmeticExpression(
					new LocalVariable(4),
					new LocalVariable(2),
					ExpressionConstants.MULT);
			ArithmeticExpression loc_4_mult_loc_2_plus_loc_1 =
				(
					ArithmeticExpression) ArithmeticExpression
						.getArithmeticExpression(
					loc_4_mult_loc_2,
					new LocalVariable(1),
					ExpressionConstants.ADD);
			Formula invariant =
				new Predicate2Ar(
					new LocalVariable(3),
					loc_4_mult_loc_2_plus_loc_1,
					PredicateSymbol.EQ);
			Expression[] loopModif =
				new Expression[] { modif_loc1, modif_loc4 };
			SingleLoopSpecification loopSpec =
				new SingleLoopSpecification(5, loopModif, invariant, null);
			SingleLoopSpecification[] loopSpecs =
				new SingleLoopSpecification[] { loopSpec };
			loopSpecification = new LoopSpecification(loopSpecs);

		}*/

	}

	/**
	 * @param gens
	 */
	private void setLocalVariables(MethodGen m , ConstantPoolGen cpGen) {
		LocalVariableGen[] locVarTable = m.getLocalVariables();
		if (locVarTable == null) {
			return;
		}
		
		if (locVarTable.length <= 0) {
			return;
		}
		
		localVariables = new RegisterTable();
		
		for (int i = 0; i < locVarTable.length ; i++) {
			JavaType type = JavaType.getJavaType( locVarTable[i].getType());
			BCLocalVariable lv = new BCLocalVariable(locVarTable[i].getLocalVariable(cpGen), type, this);
			localVariables.addRegister( lv);
		}
	}
	/**
	 * 
	 *  //modified the search of the variable at index : because of the realisation of bcel : if there is a 
	 *local variable coded with two bytes the local variable array is diminuished with 1
	 *  
	 * get the local variable that is at index i
	 * 
	 * @param i -
	 *            index of the local variable
	 * @return local variable at index i
	 */
	public BCLocalVariable getLocalVariableAtIndex(int i) {
		//		// commented because of the bcel realisation
		//		//return localVariables[i]
		//		int bcelIndex = i;
		//		for (int s= 0; s<= i;s++) {
		//			if (localVariables[i].getLength() == 2 ) {
		//				bcelIndex = bcelIndex - 1;
		//			}
		//		}
		
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
	public Formula getExsuresForException(JavaObjectType _exc_type) {
		if (methodSpecification == null) {
			return Predicate0Ar.FALSE;
		}
		SpecificationCase[] specCases =
			methodSpecification.getSpecificationCases();
		ExsuresTable exsures = specCases[0].getExsures();
		if (exsures == null) {
			return Predicate0Ar.FALSE;
		}
		Formula exsuresPredicate =
			exsures.getExcPostconditionFor(_exc_type.getSignature());
		return exsuresPredicate;
	}
	/**
	 * @return the predicate that must be true in the state after the execution
	 *         of the method
	 */
	 /*
	public Formula getPostcondition() {
		if (methodSpecification == null) {
			return Predicate.TRUE;
		}
		SpecificationCase[] specCases =
			methodSpecification.getSpecificationCases();
		return specCases[0].getPostcondition();
	}*/
/*	*//**
	 * @return the predicate that must be true in the state before the
	 *         execution of the method
	 *//*
	public Formula getPrecondition() {
		if (methodSpecification == null) {
			return Predicate.TRUE;
		}
		SpecificationCase[] specCases =
			methodSpecification.getSpecificationCases();
		return specCases[0].getPrecondition();
	}*/
	/**
	 * @return
	 */
	public Trace getTrace() {
		return trace;
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
	 * @throws IllegalLoopException
	 */
	protected void initTrace() throws IllegalLoopException {
		if (trace != null) {
			return;
		}
		setTrace(new Trace(this));
	}

	public static BCInstruction[] wrapByteCode(
		MethodGen _mg,
		BCMethod meth,
		BCConstantPool constantPool,
		RegisterTable _lv) {
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
					JavaType _type =
						JavaType.getJavaRefType(
							((TypedInstruction) _iharr[i].getInstruction())
								.getType(_bcel_cp)
								.getSignature());
					if ((instr instanceof AALOAD)
						|| (instr instanceof BALOAD)
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
					//cp instructions
				} else if (instr instanceof CPInstruction) {
					JavaType _type =
						JavaType.getJavaRefType(
							((TypedInstruction) instr)
								.getType(_bcel_cp)
								.getSignature());
					// the class where the field or method is declared
					JavaType _classType = null;
					if (instr instanceof FieldOrMethod) {
						_classType =
							JavaType.getJavaRefType(
								((FieldOrMethod) instr)
									.getClassType(_bcel_cp)
									.getSignature());
					}
					if (instr instanceof InvokeInstruction) {
						if (instr instanceof INVOKEVIRTUAL) {
							_bc[i] =
								new BCINVOKEVIRTUAL(
									_iharr[i],
									_type,
									_classType,
									constantPool);
						} else if (instr instanceof INVOKESTATIC) {
							_bc[i] =
								new BCINVOKESTATIC(
									_iharr[i],
									_type,
									_classType,
									constantPool);
						} else if (instr instanceof INVOKESPECIAL) {
							_bc[i] =
								new BCINVOKESPECIAL(
									_iharr[i],
									_type,
									_classType,
									constantPool);
						} else if (instr instanceof INVOKEINTERFACE) {
							_bc[i] =
								new BCINVOKEINTERFACE(
									_iharr[i],
									_type,
									_classType,
									constantPool);
						}

					} else if (instr instanceof PUTFIELD) {
						_bc[i] =
							new BCPUTFIELD(
								_iharr[i],
								_type,
								_classType,
								constantPool);
					} else if (instr instanceof GETFIELD) {
						_bc[i] =
							new BCGETFIELD(
								_iharr[i],
								_type,
								_classType,
								constantPool);
					} else if (instr instanceof GETSTATIC) {
						_bc[i] =
							new BCGETSTATIC(
								_iharr[i],
								_type,
								_classType,
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
						JavaArrType arrType = JavaType.getJavaArrTypeWithBasicType(_type);
						_bc[i] = new BCANEWARRAY(_iharr[i], arrType);
					} else if (instr instanceof MULTIANEWARRAY) {
						_bc[i] = new BCMULTIANEWARRAY(_iharr[i], _type);
					} else if (instr instanceof INSTANCEOF) {
						_bc[i] = new BCINSTANCEOF(_iharr[i], _type);
					}
				} else if (instr instanceof NEWARRAY) {
					JavaType _type =
						JavaType.getJavaRefType(
							((NEWARRAY) instr).getType().getSignature());
					_bc[i] = new BCNEWARRAY(_iharr[i], _type);
				} else if (instr instanceof ARRAYLENGTH) {
					_bc[i] = new BCARRAYLENGTH(_iharr[i]);
				} else if (instr instanceof LocalVariableInstruction) {
					int localVarIndex =
						((LocalVariableInstruction) instr).getIndex();
					BCLocalVariable locVar = null;
					if ( _lv != null) {
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
						_bc[i] = new BCICONST(_iharr[i]);
					} else if (instr instanceof SIPUSH) {
						_bc[i] = new BCSIPUSH(_iharr[i]);
					}
				}
				if (_bc[i] == null) {
					return null;
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
	public int getNumberArguments() {
		return argNames.length;
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
		if (trace == null) {
			return;
		}
		//commented for test purposes
		/*Util.dump("wp for " + name);*/
		if (methodSpecification == null) {
			trace.wp(Predicate0Ar.TRUE, null);
			return;
		}
		SpecificationCase[] specCases =
			methodSpecification.getSpecificationCases();
		Formula invariant = clazz.getClassInvariant();
		Formula historyConstraints = clazz.getHistoryConstraints();
		if (specCases == null) {
			Formula post = Predicate0Ar.TRUE;
			if ( invariant != null ) {
				post = invariant;
			}
			if (historyConstraints != null) {
				post = Formula.getFormula( post , (Formula)historyConstraints.copy(), Connector.AND);
			}
			trace.wp(post, null);
			return;
		}
		for (int i = 0; i < specCases.length; i++) {
			Formula stateCondition = clazz.getVectorAtStateToHold(ClassStateVector.RETURN_STATE, specCases[i].getModifies() );	
			Formula post = (Formula)specCases[i].getPostcondition().copy();
			post = Formula.getFormula( post, stateCondition, Connector.AND  );
			
			if ( invariant != null ) {
				post = Formula.getFormula( post,  (Formula)invariant.copy(), Connector.AND);
			}
			if (historyConstraints != null) {
				post = Formula.getFormula( post , (Formula)historyConstraints.copy(), Connector.AND);
			}
			trace.wp(
				post,
				specCases[i].getExsures());
			Formula casePrecondition = (Formula)specCases[i].getPrecondition().copy();
			Formula gPrecondition =  methodSpecification.getPrecondition();
			Formula precondition = Formula.getFormula(casePrecondition, gPrecondition, Connector.AND);
			setWP( precondition);
			initWp();
		}
		/*Util.dump(" Proof obligation " + getName());*/
		Util.dump(proofObligation);
	}
	
	/**
	 * reinitiliases to nul all the wps stored in the entrypoint instructions
	 */
	private void initWp() {
		trace.initWp();
		
	}

	/**
	 * generates the proof obligations for one specification case
	 * @param precondition
	 */
	private void setWP(Formula precondition ) {
		Vector v = trace.getWP();
		if (proofObligation == null) {
			proofObligation = new Vector();
		}
		Formula invariant = clazz.getClassInvariant();
		for (int i = 0; i < v.size();i++) {
			 
			Formula wp = (Formula)v.elementAt(i);
			wp  = Formula.getFormula(precondition, wp, Connector.IMPLIES );
			// if not a constructor then then  the invariant should hold in the prestate of method execution 
			if (getName() != "<init>" ) {
				wp = Formula.getFormula( wp , invariant, Connector.AND );
			}
			proofObligation.add(wp);
			
		}
		
	} 
	
	public ExceptionHandler[] getExceptionHandlers() {
		return exceptionHandlerTable.getExcHandlers();
	}
	/**
	 * Returns the name.
	 * @return String
	 */
	public String getName() {
		return name;
	}

	/**
	 * Sets the name.
	 * @param name The name to set
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * Returns the signature.
	 * @return String
	 */
	public String getSignature() {
//		signature =  MethodSignature.getSignature(getArgTypes() , getReturnType() );
		return signature;
	}

	


	/**
	 * Returns the argNames.
	 * @return String[]
	 */
	public String[] getArgNames() {
		return argNames;
	}

	/**
	 * Sets the argNames.
	 * @param argNames The argNames to set
	 */
	public void setArgNames(String[] argNames) {
		this.argNames = argNames;
	}

	/**
	 * Returns the bytecode.
	 * @return BCInstruction[]
	 */
	public BCInstruction[] getBytecode() {
		return bytecode;
	}

	public String toString() {
		return clazz.getName() + "." + name +  "" +  signature;
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
	
	
	///////////////////////////////////////////
	///////////////////////////////////////////
	/////Memory ALlocation//////////////////
	////////////////////////////////////////
	///////////////////////////////////////
	private boolean checked = false ;
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
	 * @param allocations The allocations to set.
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
	
	//////////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////////
	////////////////Memory constraint consumption specification/////
	////////////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////////
	public void initMethodSpecForMemoryConsumption() {
		// requires MemUsed + alloc <= Max
		FieldAccess memUsed =  new FieldAccess( MemUsedConstant.MemUsedCONSTANT);
		Expression upperBoundForConsum  = new NumberLiteral(allocations);
		Expression memUsed_pluc_upperBound = ArithmeticExpression.getArithmeticExpression(memUsed, upperBoundForConsum, ExpressionConstants.ADD );	
		Formula requiresFormula =  
				new Predicate2Ar(memUsed_pluc_upperBound , MethodAllocation.MAX , PredicateSymbol.LESSEQ);

		// ensures MemUsed <= old(MemUsed) + alloc
		Expression oldMemUsed_plus_upperBound = ArithmeticExpression.getArithmeticExpression(new OLD(memUsed), upperBoundForConsum,ExpressionConstants.ADD );		
		Formula ensuresFormula = new Predicate2Ar(memUsed.copy(), oldMemUsed_plus_upperBound, PredicateSymbol.LESSEQ );
		
		// modifies MemUsed 
		ModifiesSet modifies = null;		
		ModifiesExpression modExpr = new ModifiesIdent(new FieldAccess( MemUsedConstant.MemUsedCONSTANT),clazz.getConstantPool() );
		ModifiesSet modifSet = new ModifiesSet(new ModifiesExpression[]{modExpr} , clazz.getConstantPool() );

		
		// set the specification generated for every method
		SpecificationCase specCase = new SpecificationCase(
				requiresFormula,
				ensuresFormula,				
				modifSet,
				null);		
		methodSpecification = new MethodSpecification(Predicate0Ar.TRUE, new SpecificationCase[]{specCase});	
	}
}
