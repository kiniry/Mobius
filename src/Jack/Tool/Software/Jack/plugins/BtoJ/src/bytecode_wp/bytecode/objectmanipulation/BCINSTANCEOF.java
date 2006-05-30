/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.objectmanipulation;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * instanceof
 * 
 * Operation: Determine if object is of given type
 * 
 * Format : instanceof 	 indexbyte1 	indexbyte2
 * 
 * Operand Stack:  ..., objectref ==> ..., result
 * 
 * Description:The objectref, which must be of type reference, is popped from the operand stack. 
 * The unsigned indexbyte1 and indexbyte2 are used to construct an index into the runtime constant pool of 
 * the current class, where the value of the index is (indexbyte1 << 8) | indexbyte2. The runtime constant pool item 
 * at the index must be a symbolic reference to a class, array, or interface type. The named class, array, or interface type 
 * is resolved .If objectref is not null and is an instance of the resolved class or array or 
 * implements the resolved interface, the instanceof instruction pushes an int result of 1 as an int on the operand stack. 
 * Otherwise, it pushes an int result of 0. 	
 * 
 * Linking Exceptions:  During resolution of symbolic reference to the class, array, or interface type, any of the exceptions 
 * documented in the JVM (Section 5.4.3.1) can be thrown.
 *
 * Notes : The instanceof instruction is very similar to the checkcast instruction. It differs in 
 * its treatment of null, 
 * its behavior when its test fails (checkcast throws an exception, instanceof pushes a result code), 
 * and its effect on the operand stack.
 * 
 * 
 * 
 *  wp	=( !( S(t) <: Type)  || S(t) == null) ==> psi^n[S(t) <-- 0 ] 
 * 			&&
 * 		  (S(t) <: Type)  && S(t) != null )==> psi^n[S(t) <-- 1 ] 
 */
public class BCINSTANCEOF
	extends BCInstruction
	implements BCCPInstruction {
	private JavaType type;
	private int cpIndex;

	/**
	 * @param _instruction
	 */
	public BCINSTANCEOF(InstructionHandle _instruction, JavaType _type) {
		super(_instruction);
		setIndex(((CPInstruction) _instruction.getInstruction()).getIndex());
		setType(_type);
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#setIndex(int)
	 */
	public void setIndex(int _index) {
		cpIndex = _index;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#getIndex()
	 */
	public int getIndex() {
		return cpIndex;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
		type = _type;
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;

//		Stack topStack = new Stack(Expression.COUNTER);

		//S(t) <: Type
		Formula topStackSubType =
			new Predicate2Ar(
				new TYPEOF(new Stack(Expression.COUNTER) ),
				getType(),
				PredicateSymbol.SUBTYPE);

		//S(t) != null
		Formula topStackNotNull =
			Formula.getFormula(
			new Predicate2Ar(new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ), 
			Connector.NOT );

		//S(t) <: Type && S(t) != null
		Formula condition0 =
		Formula.getFormula(topStackSubType, topStackNotNull, Connector.AND);
		Formula condition0Implies = (Formula)_normal_Postcondition.copy();

		//psi^n[S(t) <-- 1] 
		condition0Implies =
		(Formula)condition0Implies.substitute(new Stack(Expression.COUNTER), new NumberLiteral(1));

		// 	S(t) <: Type && S(t) != null  ==> psi^n[S(t) <-- 1] 
		Formula wpTopStackisOfSubtype =
		Formula.getFormula(condition0, condition0Implies, Connector.IMPLIES);

	//////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////////////
	
		// !( S(t) <: Type)
		Formula topStackNotSubType =
			Formula.getFormula(topStackSubType, Connector.NOT);

		//S(t) == null
		Formula topStackNull =
			new Predicate2Ar(new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ);
	
		//	!( S(t) <: Type)  || S(t) == null
		Formula condition1 = Formula.getFormula(topStackNotSubType, topStackNull, Connector.OR);
		Formula condition1implies =  (Formula)_normal_Postcondition.copy();
		
		//psi^n[S(t) <-- 0 ]
		condition1implies = (Formula)condition1implies.substitute(new Stack(Expression.COUNTER), new NumberLiteral(0) );
		
		//	!( S(t) <: Type)  || S(t) == null ==> psi^n[S(t) <-- 0 ]
		Formula wpTopStackisOfNotSubtype = Formula.getFormula (condition1, condition1implies, Connector.IMPLIES);
		
//		wp	=( !( S(t) <: Type)  || S(t) == null) ==> psi^n[S(t) <-- 0 ] 
//		 			&&
//		 		  (S(t) <: Type)  && S(t) != null )==> psi^n[S(t) <-- 1 ] 
		wp = Formula.getFormula(wpTopStackisOfNotSubtype, wpTopStackisOfSubtype, Connector.AND);
		return wp;
	}

	
	
	
	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {

		VCGPath vcCase = (VCGPath) vcs.copy();
		
		//S(t) <: Type
		Formula topStackSubType =
			new Predicate2Ar(
				new TYPEOF(new Stack(Expression.COUNTER) ),
				getType(),
				PredicateSymbol.SUBTYPE);

		//S(t) != null
		Formula topStackNotNull =
			Formula.getFormula(
			new Predicate2Ar(new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ), 
			Connector.NOT );

/*		//S(t) <: Type && S(t) != null
		Formula condition0 =
		Formula.getFormula(topStackSubType, topStackNotNull, Connector.AND);
		Formula condition0Implies = (Formula)_normal_Postcondition.copy();*/

		//psi^n[S(t) <-- 1] 
		vcs.substitute(new Stack(Expression.COUNTER), new NumberLiteral(1));

		Integer key1 = vcs.addHyp( getPosition(), topStackNotNull);
		vcs.addHypsToVCs(key1);
		Integer key2 = vcs.addHyp( getPosition(), topStackSubType);
		vcs.addHypsToVCs(key2);
		
		

	//////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////////////
	
		// !( S(t) <: Type)
		Formula topStackNotSubType =
			Formula.getFormula(topStackSubType, Connector.NOT);

		//S(t) == null
		Formula topStackNull =
			new Predicate2Ar(new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ);
	
		//	!( S(t) <: Type)  || S(t) == null
		Formula condition1 = Formula.getFormula(topStackNotSubType, topStackNull, Connector.OR);

		
		//psi^n[S(t) <-- 0 ]
		vcCase.substitute(new Stack(Expression.COUNTER), new NumberLiteral(0) );
		
		//	!( S(t) <: Type)  || S(t) == null ==> psi^n[S(t) <-- 0 ]
		Integer key3 = vcCase.addHyp(getPosition(), condition1);
		vcCase.addHypsToVCs(key3);
		Integer key4 = vcCase.addHyp(getPosition(), topStackNull);
		vcCase.addHypsToVCs(key4);
		
		vcs.merge(vcCase);
		return vcs;
	}

}
