/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;

import constants.BCConstantClass;
import constants.BCConstantMethodRef;

import application.JavaApplication;
import bcclass.BCClass;
import bcclass.BCConstantPool;
import bcclass.BCMethod;
import bcclass.attributes.ExsuresTable;
import bcexpression.ArithmeticExpression;
import bcexpression.EXCEPTIONVariable;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.LocalVariableAccess;
import bcexpression.NumberLiteral;
import bcexpression.Variable;

import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.RESULT;
import bcexpression.ref.Reference;
import bcexpression.vm.Stack;

import utils.FreshIntGenerator;
import formula.Connector;
import formula.Formula;
import formula.Quantificator;
import formula.QuantifiedFormula;

/**
 * @author mpavlova
 *
 * Operation : Invoke instance method; dispatch based on class
 *
 * Format :  invokevirtual 	indexbyte1 	indexbyte2 	
 * 
 * invokevirtual = 182 (0xb6)
 *
 * Operand Stack :  ..., objectref, [arg1, [arg2 ...]]  == >...
 *
 * 
 */
public class BCINVOKEVIRTUAL extends BCFieldOrMethodInstruction {

	//	/private JavaType[] argTypes;

	/**
	 * @param _instruction - the corresponding bcel data structure
	 * @param _type
	 * @param _classType
	 * @param _cp constant
	 * pool of the class where this executuion is declared
	 */
	public BCINVOKEVIRTUAL(
		InstructionHandle _instruction,
		JavaType _type,
		JavaType _classType,
		BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
		setExceptionsThrown( new JavaObjectType[]{ (JavaObjectType)JavaObjectType.getJavaRefType( ClassNames.NULLPOINTERException) });		
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp = null;
		BCConstantMethodRef method_constant =
			(BCConstantMethodRef) (getConstantPool().getConstant(getIndex()));
		String clazz_name =
			((BCConstantClass) (getConstantPool()
				.getConstant(method_constant.getClassIndex())))
				.getName();

		//find the class where the called method is declared 
		BCClass clazz = JavaApplication.getClass(clazz_name);
		// get the method instance
		BCMethod method = clazz.lookupMethod(method_constant.getName());

		//take the method pre and postconditons
		Formula precondition = method.getPrecondition().copy();
		int number_args = method.getNumberArguments();
		ArithmeticExpression counter_minus_arg_num =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				Expression.COUNTER,
				new NumberLiteral(number_args),
				ExpressionConstants.SUB);

		//S( t - arg_num(method(index) ))
		Stack stack_minus_arg_number = new Stack(counter_minus_arg_num);

		///////////////////////////////////////
		////////////////////////////////////////////////////////////
		/////////////////////////////////////////////////////////////////////
		Formula postcondition = method.getPostcondition().copy();
		//WITH withResult = new WITH(new RESULT());
		RESULT result = Expression._RESULT;
		Variable fresh_result =
			new Variable(FreshIntGenerator.getInt(), method.getReturnType());

		Expression[] modifies = method.getModifies();
		Expression[] modifies1 = null;
		// check if the called method modifies any expression
		if ((modifies != null) && (modifies.length > 0)) {
			modifies1 = new Expression[modifies.length];
			//make a copy of every of the modified expressions 
			for (int i = 0; i < modifies.length; i++) {
				modifies1[i] = modifies[i].copy();
			}
		}

		//post(method(index) )[o with result <-- fresh ] 
		if (method.getReturnType() != JavaType.JavaVOID) {
			postcondition = postcondition.substitute(result, fresh_result);
		}

		// substitute all the local variables in the precondition, the postcondition
		// and the  expressions in the modifies clause of the called method 
		// with the values that are in the stack . 
		// do these substitutions : 
		// local(0) <-- S( t - arg_num(method(index) )  + 0), 
		// local(1) <-- S( t - arg_num(method(index) )  + 1),  
		// local(i) <-- S( t - arg_num(method(index) )  + i)
		for (int i = 0; i < number_args; i++) {
			ArithmeticExpression counter_minus_arg_num_plus_i =
				(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
					counter_minus_arg_num,
					new NumberLiteral(i),
					ExpressionConstants.SUB);
			Stack stack_at_counter_minus_arg_num_plus_i =
				new Stack(counter_minus_arg_num_plus_i);
			LocalVariableAccess local_i = new LocalVariableAccess(i);
			
			//pre(method(index) )[ o with local(i) <-- S( t - arg_num(method(index) ) + i )]
			precondition =
				precondition.substitute(
					local_i,
					stack_at_counter_minus_arg_num_plus_i);

			//post(method(index) )[o with result <-- fresh ] [ o with local(i) <-- S(t - arg_num(method(index)) + i)]
			postcondition =
				postcondition.substitute(
					local_i,
					stack_at_counter_minus_arg_num_plus_i);

			if ((modifies1 != null) && (modifies1.length > 0)) {
				for (int k = 0; k < modifies1.length; k++) {
					modifies1[k] =
						modifies1[k].substitute(
							local_i,
							stack_at_counter_minus_arg_num_plus_i);
				}
			}
		}

		// psi^n[ t < t -  arg_num(method(index)) ]
		Formula _normal_Postcondition1 =
			_normal_Postcondition.substitute(
				Expression.COUNTER,
				counter_minus_arg_num);

		//psi^n[ t < t -  arg_num(method(index)) ][ S(t -  arg_num(method(index)) ) <-- fresh]
		_normal_Postcondition1 =
			_normal_Postcondition1.substitute(
				stack_minus_arg_number,
				fresh_result);

		// in case of normal termination this formula must hold
		// post(method(index) )[o with result <-- fresh ] [ o with local(i) <-- S(t - arg_num(method(index)) + i)] 
		// ==> 
		// psi^n[ t < t -  arg_num(method(index)) ][ S(t -  arg_num(method(index)) ) <-- fresh]
		Formula wpNormal =
		Formula.getFormula(
				postcondition,
				_normal_Postcondition1,
				Connector.IMPLIES);
		////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////	
		// if the modifies clause of the called method is not empty then quantify 
		Quantificator[] qunatificators = new Quantificator[modifies1.length];
		if ((modifies1 != null) && (modifies1.length > 0)) {

			for (int i = 0; i < modifies1.length; i++) {
				qunatificators[i] =
					new Quantificator(Quantificator.FORALL, modifies1[i]);
			}
			wpNormal = new QuantifiedFormula(wpNormal, qunatificators);
		}
		wp = Formula.getFormula(wpNormal, precondition, Connector.AND);
		////////////////////////////////////////////////////
		//////////exceptional termination for any exception that may be thrown
		Formula[] wpForExcTermination = null;
		JavaObjectType[] exceptionsThrown = method.getExceptionsThrown();
		if ((exceptionsThrown != null) && (exceptionsThrown.length > 0)) {
			wpForExcTermination = new Formula[exceptionsThrown.length];
			Formula excPostOfCalledMethodForExc;
			Formula excPostOfThisMethodForExc;
			for (int i = 0; i < exceptionsThrown.length; i++) {
				excPostOfCalledMethodForExc =
					method.getExsuresForException(exceptionsThrown[i]).copy();
				// substitute the instance of the exception object in the exceptional
				// postcondition
				excPostOfCalledMethodForExc.substitute(
					new EXCEPTIONVariable(
						FreshIntGenerator.getInt(),
						exceptionsThrown[i]),
					new Reference(
						FreshIntGenerator.getInt(),
						exceptionsThrown[i]));

				excPostOfThisMethodForExc =
					getWpForException(exceptionsThrown[i], _exc_Postcondition);

				wpForExcTermination[i] =
				Formula.getFormula(
						excPostOfCalledMethodForExc,
						excPostOfThisMethodForExc,
						Connector.IMPLIES);
				if (qunatificators != null) {
					wpForExcTermination[i] =
						new QuantifiedFormula(
							wpForExcTermination[i],
							qunatificators);
				}
			}
		}
		if (wpForExcTermination != null) {
			Formula wpExc = Formula.getFormula(wpForExcTermination, Connector.AND);
			wp = Formula.getFormula(wp, wpExc, Connector.AND);
		}
		// exceptional termination
		return wp;
	}
}
