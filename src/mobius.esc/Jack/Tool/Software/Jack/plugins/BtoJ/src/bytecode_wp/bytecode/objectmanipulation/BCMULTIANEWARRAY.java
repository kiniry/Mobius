package bytecode_wp.bytecode.objectmanipulation;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.MULTIANEWARRAY;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.Variable;
import bytecode_wp.bcexpression.javatype.ClassNames;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.ref.ArrayReference;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCAllocationInstruction;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.formula.Quantificator;
import bytecode_wp.formula.QuantifiedFormula;
import bytecode_wp.utils.FreshIntGenerator;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *  
 * multianewarray
 *
 * Operation : Create new multidimensional array
 *  
 * Format : multianewarray 	indexbyte1 	indexbyte2 	 dimensions 	
 * 
 * Runtime Exception : Otherwise, if any of the dimensions values on the operand stack are
 * less than zero, the multianewarray instruction throws a NegativeArraySizeException.
 * 
 * Operand Stack : ..., count1, [count2, ...] ==>  ..., arrayref
 */
public class BCMULTIANEWARRAY
	extends BCAllocationInstruction
	implements BCCPInstruction {

	private int cpIndex;
	private JavaType type;

	private int dimensions;

	public BCMULTIANEWARRAY(InstructionHandle _instruction, JavaType _type)  {
		super(_instruction, _type);
		dimensions =
			((MULTIANEWARRAY) _instruction.getInstruction()).getDimensions();
		setIndex(((MULTIANEWARRAY) _instruction.getInstruction()).getIndex());
		setType(_type);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.NEGATIVEARRAYSIZEException) });
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
		return null;
	}

	
	
	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		///////////////////////////////////////////////////
		//////////////////normal termination
		//////////////////////////////////////////////////
		// for all i : { i <= t and i > t - dimensions }
		Variable boundVar =
			new Variable(FreshIntGenerator.getInt(), JavaType.JavaINT);

		// i <= t
		Formula i_less_counter =
			new Predicate2Ar(
				boundVar,
				Expression.COUNTER,
				PredicateSymbol.LESSEQ);

		//  t - dims 
		ArithmeticExpression counter_minus_dims =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				Expression.COUNTER,
				new NumberLiteral(dimensions),
				ExpressionConstants.SUB);

		// i > t -dims
		Formula i_bigger_dims =
			new Predicate2Ar(boundVar, counter_minus_dims, PredicateSymbol.GRT);

		// i <= t and i >t  
		Formula domain =
		Formula.getFormula(i_less_counter, i_bigger_dims, Connector.AND);

		//forall i. 
		Quantificator quantificator =
			new Quantificator(Quantificator.FORALL, boundVar);

	Stack _anyArrLength = new Stack(boundVar);
		// (i > t - dims and i < t) ==> S(i) >= 0  
		Formula opened_formula =
			new Predicate2Ar(
				_anyArrLength,
				new NumberLiteral(0),
				PredicateSymbol.GRTEQ);
		opened_formula =Formula.getFormula(domain, opened_formula , Connector.IMPLIES);

		//forall  i : int.(  (i > t - dims and i < t) ==> S(i) >= 0)
		QuantifiedFormula conditionForNormalTermination =
			new QuantifiedFormula(opened_formula, quantificator);

		// t- dimensions
		Expression counterMinusArrayDim_minus_1 =
			ArithmeticExpression.getArithmeticExpression(
				Expression.COUNTER,
				new NumberLiteral(dimensions - 1),
				ExpressionConstants.SUB);

		//psi^n[t <-- t -dimensions ]
		vcs.substitute(
				Expression.COUNTER,
				counterMinusArrayDim_minus_1);
		Stack topStack_minusArrDim_minus_1 =
			new Stack(counterMinusArrayDim_minus_1);

		Stack lengthAtLevel;
		ArrayReference ref = null;
		for (int i = 0; i < dimensions; i++) {
			Expression counter =
				ArithmeticExpression.getArithmeticExpression(
					Expression.COUNTER,
					new NumberLiteral(i),
					ExpressionConstants.SUB);
//			lengthAtLevel = new Stack(counter);
			if (ref == null) {
				//if we are at the dimension 0
				ref =
					new ArrayReference(
						FreshIntGenerator.getInt(),
						getType(),
				new Stack(counter));
				continue;
			}
			//otherwise give a reference that represents an element from the array 
			ref =
				new ArrayReference(
					FreshIntGenerator.getInt(),
					getType(),
			/*new Stack(counter),*/
					ref);
		}
//		reference is different from null 
		Formula refNeqNull = new Predicate2Ar( Expression._NULL, ref , PredicateSymbol.NOTEQ);
		Integer  keyRefDiffNull = vcs.addHyp(getPosition(), refNeqNull);
		vcs.addHypsToVCs( keyRefDiffNull);
		
		//psi^n[t <-- t -dimensions ][S( t - dims + 1) < -- new multiarr]
		vcs.substitute(topStack_minusArrDim_minus_1, ref);
		
		Integer key = vcs.addHyp( getPosition(), conditionForNormalTermination);
		vcs.addHypsToVCs(key);
		


		///////////////////////////////////////////////////		
		//exceptional termination
		////////////////////////////////////////////
		Variable boundVar1 =
			new Variable(FreshIntGenerator.getInt(), JavaType.JavaINT);

		///////////////////////////
		// i <= t
		Formula i_less_counter1 =
			new Predicate2Ar(
				boundVar1,
				Expression.COUNTER,
				PredicateSymbol.LESSEQ);

		//  t - dims 
		ArithmeticExpression counter_minus_dims1 =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				Expression.COUNTER,
				new NumberLiteral(dimensions),
				ExpressionConstants.SUB);

		// i > t -dims
		Formula i_bigger_dims1 =
			new Predicate2Ar(
				boundVar1,
				counter_minus_dims1,
				PredicateSymbol.GRT);

		// i <= t and i >t  
		Formula domain1 =
		Formula.getFormula(i_less_counter1, i_bigger_dims1, Connector.AND);

		// exista i. (i > t - dims and i < t)
		Quantificator quantificator1 =
			new Quantificator(Quantificator.EXISTS, boundVar1);

		Stack _anyArrLength1 = new Stack(boundVar1);

		// S(i) >= 0  
		Formula opened_formula1 =
			new Predicate2Ar(
				_anyArrLength1,
				new NumberLiteral(0),
				PredicateSymbol.LESS);

		//forall  i. (i > t - dims and i < t ==> S(i) <= 0)
		QuantifiedFormula conditionForExcTermination =
			new QuantifiedFormula(Formula.getFormula(domain1, opened_formula1, Connector.IMPLIES ), quantificator1);

		//psi^(e)
		VCGPath excT =
			getWpForException(config,
				(JavaObjectType) JavaType.getJavaRefType(
					"Ljava/lang/NegativeArraySizeException;"));
		Integer key2 = excT.addHyp(getPosition(), conditionForExcTermination);
		excT.addHypsToVCs(key2);
		
		
		vcs.merge(excT);
		return vcs;
	}

}
