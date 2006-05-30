/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.objectmanipulation;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.javatype.ClassNames;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCExceptionThrower;
import bytecode_wp.constants.ArrayLengthConstant;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.Hypothesis;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 * Operation Get length of array
 */
public class BCARRAYLENGTH extends BCExceptionThrower {

	/**
	 * @param _instruction
	 */
	public BCARRAYLENGTH(InstructionHandle _instruction) {
		super(_instruction);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.NULLPOINTERException) });

	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return null;

	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
//		wp in case of normal termination
		Formula objNotNull =
			Formula.getFormula(
					new Predicate2Ar( new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ), Connector.NOT);
		//S(t).length
		FieldAccess arrLength =
			new FieldAccess(ArrayLengthConstant.ARRAYLENGTHCONSTANT,  new Stack(Expression.COUNTER));
		vcs.substitute( new Stack(Expression.COUNTER), arrLength);
		Integer hObjNotNull = vcs.addHyp( getPosition(), objNotNull);
		vcs.addHypsToVCs( hObjNotNull);

		//wp in case of throwing exception
		Formula objNull =
			new Predicate2Ar( new Stack(Expression.COUNTER), Expression._NULL, PredicateSymbol.EQ);
			
			// in case the array object is null - Ljava/lang/NullPointerException; is thrown 
		VCGPath excPrecondition =
			getWpForException(config,
				getExceptionsThrown()[0]);
		
		Integer  hObjNull = excPrecondition.addHyp( getPosition(), objNull);
		excPrecondition.addHypsToVCs( hObjNull);
		
		vcs.merge( excPrecondition);
		return vcs;
	}

}
