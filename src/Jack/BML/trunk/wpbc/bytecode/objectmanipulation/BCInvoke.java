/*
 * Created on Jun 30, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;
import modifexpression.Everything;
import modifexpression.ModifiesExpression;
import modifexpression.Nothing;

import org.apache.bcel.generic.InstructionHandle;
import bc.io.ReadAttributeException;
import bcclass.BCConstantPool;
import bcclass.attributes.ExsuresTable;
import bcclass.attributes.MethodSpecification;
import bcclass.attributes.ModifiesSet;
import bcclass.attributes.SpecificationCase;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import formula.Formula;
import constants.BCConstantClass;
import constants.BCConstantMethodRef;
import application.JavaApplication;
import bcclass.BCClass;
import bcclass.BCMethod;
import bcclass.utils.MethodSignature;
import bcexpression.ArithmeticExpression;
import bcexpression.ConstantVariable;
import bcexpression.EXCEPTIONVariable;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.LocalVariable;
import bcexpression.NumberLiteral;
import bcexpression.Variable;
import bcexpression.jml.RESULT;
import bcexpression.vm.Stack;
import utils.FreshIntGenerator;
import utils.Util;
import formula.Connector;
import formula.Quantificator;
import formula.atomic.Predicate;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCInvoke extends BCFieldOrMethodInstruction {
	/**
	 * @param _instruction
	 * @param _type
	 * @param _classType
	 * @param _cp
	 */
	public BCInvoke(InstructionHandle _instruction, JavaType _type,
			JavaType _classType, BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula,
	 *      specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition,
			ExsuresTable _exc_Postcondition) {
		Formula wp = null;
		BCConstantMethodRef method_constant = (BCConstantMethodRef) (getConstantPool()
				.getConstant(getIndex()));
		String clazz_name = ((BCConstantClass) (getConstantPool()
				.getConstant(method_constant.getClassIndex()))).getName();
		//find the class where the called method is declared
		BCClass clazz = JavaApplication.Application.getClass(clazz_name);
		// get the method instance
		BCMethod method = null;
		
		try {
			method = clazz.lookupMethod(MethodSignature.getSignature(
					method_constant.getName(), method_constant.getSignature()));
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
		//take the method pre and postconditons
		/* Formula precondition = (Formula) method.getPrecondition().copy(); */
		int number_args = method.getNumberArguments();
		ArithmeticExpression counter_minus_arg_num = (ArithmeticExpression) ArithmeticExpression
				.getArithmeticExpression(Expression.COUNTER, new NumberLiteral(
						number_args), ExpressionConstants.SUB);
		//S( t - arg_num(method(index) ))
		//		Stack stack_minus_arg_number = new Stack(counter_minus_arg_num);
		///////////////////////////////////////
		////////////////////////////////////////////////////////////
		/////////////////////////////////////////////////////////////////////
		/*
		 * Formula postcondition = (Formula) method.getPostcondition().copy();
		 */
		MethodSpecification methodSpecification = method
				.getMethodSpecification();
		Formula requiresCalledMethod = null;
		SpecificationCase[] specCases = null;
		if ( methodSpecification == null) {
			requiresCalledMethod =Predicate.TRUE;
		} else { 
			requiresCalledMethod = methodSpecification.getPrecondition();
			specCases = methodSpecification
					.getSpecificationCases();
		}
		
		
		Formula wp_spec_cases = Predicate.FALSE;
		int top_minus_number_args_minus_obj_plus_res = 0;
		Variable fresh_result = null;
		if (method.getReturnType() == JavaType.JavaVOID) {
			top_minus_number_args_minus_obj_plus_res = number_args + 1;
		} else {
			top_minus_number_args_minus_obj_plus_res = number_args;
				RESULT result = Expression._RESULT;
				fresh_result = new Variable(FreshIntGenerator.getInt(), method
						.getReturnType());
		}
		ArithmeticExpression counter_minus_arg_num_plus_1 = (ArithmeticExpression) ArithmeticExpression
				.getArithmeticExpression(Expression.COUNTER,
						new NumberLiteral(
								top_minus_number_args_minus_obj_plus_res),
						ExpressionConstants.SUB);
//		psi^n[t <-- t - arg_n_plus_1 ]
		_normal_Postcondition = (Formula) _normal_Postcondition.substitute(
				Expression.COUNTER, counter_minus_arg_num_plus_1);
//		//psi^n[ S(t ) <-- fresh]
		if (fresh_result != null) {
			_normal_Postcondition = (Formula) _normal_Postcondition
					.substitute(new Stack(Expression.COUNTER), fresh_result);
		}
		if ( specCases == null ) {
			wp = Formula.getFormula(_normal_Postcondition, requiresCalledMethod, Connector.AND );
			return wp ;
		}
		for (int n = 0; n < specCases.length; n++) {
			Formula postcondition = specCases[n].getPostcondition();
			/*Formula nonModifFields = specCases[n].getConditionForNonModifiedFields();*/
			Formula modPost = specCases[n].getModifiesPostcondition();
			Formula post = (Formula)specCases[n].getPostcondition().copy();
			Formula precondition = specCases[n].getPrecondition();
			
			// quantify over the result of the invoked method
			/*Quantificator[] quantificators = null;*/
			//quantifiers for the exceptional termination
			Quantificator quantifyOnResult = null;
			//post(method(index) )[o with result <-- fresh ]
			if (method.getReturnType() != JavaType.JavaVOID) {
				RESULT result = Expression._RESULT;
				fresh_result = new Variable(FreshIntGenerator.getInt(), method
						.getReturnType());
				postcondition = (Formula) postcondition.substitute(result,
						fresh_result);
				quantifyOnResult = new Quantificator(Quantificator.FORALL,
						fresh_result);
			}
			// substitute all the local variables in the precondition, the
			// postcondition
			// and the expressions in the modifies clause of the called method
			// with the values that are in the stack .
			// do these substitutions :
			// local(0) <-- S( t - arg_num(method(index) ) + 0),
			// local(1) <-- S( t - arg_num(method(index) ) + 1),
			// local(i) <-- S( t - arg_num(method(index) ) + i)
			
			for (int i = 0; i < number_args; i++) {
				ArithmeticExpression counter_minus_arg_num_plus_i = (ArithmeticExpression) ArithmeticExpression
						.getArithmeticExpression(counter_minus_arg_num,
								new NumberLiteral(i), ExpressionConstants.SUB);
				Stack stack_at_counter_minus_arg_num_plus_i = new Stack(
						counter_minus_arg_num_plus_i);
				LocalVariable local_i = new LocalVariable(i);
				//pre(method(index) )[ o with local(i) <-- S( t -
				// arg_num(method(index) ) + i )]
				precondition = (Formula) precondition.substitute(local_i,
						stack_at_counter_minus_arg_num_plus_i);
				//post(method(index) )[o with result <-- fresh ] [ o with
				// local(i) <-- S(t - arg_num(method(index)) + i)]
				postcondition = (Formula) postcondition.substitute(local_i,
						stack_at_counter_minus_arg_num_plus_i);
				/*if (modifiesSubst != null) {
					for (int m = 0; m < modifiesSubst.length; m++) {
						modifiesSubst[m] = modifiesSubst[m].substitute(local_i,
								stack_at_counter_minus_arg_num_plus_i);
					}
				}*/
			}
			
			//psi^n[t <-- t - arg_n_plus_1 ]
		
			// in case of normal termination this formula must hold
			// post(method(index) )[result <-- fresh ] [ local(i) <-- S(t -
			// arg_num(method(index)) + i)]
			// ==>
			// psi^n[ S(t ) <-- fresh]
			Formula wpNormal = Formula.getFormula(postcondition,
					_normal_Postcondition, Connector.IMPLIES);
			
			ModifiesSet modifiesSet = specCases[n].getModifies().copy();
			/*Expression[] modifiesSubst = null;*/
			ModifiesExpression[] modifies = modifiesSet.getModifiesExpressions();
			for (int i = 0 ; i < modifies.length; i++){
				Expression constantFieldRef = modifies[i].getConstantFieldRef();
				ConstantVariable constantVar = new ConstantVariable(FreshIntGenerator.getInt()) ;
				modifies[i] = (ModifiesExpression)modifies[i].substitute(constantFieldRef, constantVar );
				wpNormal = (Formula)wpNormal.substitute( constantFieldRef , constantVar);
			}
			
			
			// if there is a value returned by the invoked method then quantify
			// over it
			if (quantifyOnResult != null) {
				wpNormal = Formula.getFormula(wpNormal, quantifyOnResult);
			}
			Formula wpSpecCase = Formula.getFormula(wpNormal, precondition, Connector.AND);
			/*Util.dump("normal wp specCase " + n + " :  " + wpSpecCase);*/	
			/////////////////////////////////////////////////////////////////////////////////////////////////////////
			////////////////////////Exceptional
			// Termination/////////////////////////////////////////////
			/////////////////////////////////////////////////////////////////////////////////////////////////////
			// if one must quantify the exceptional behaviour
			// for all (modifies ) (excPost(index, exc) ==> psi^exc(exc)) ,
			// then quantify over the same the expression
			// as in the case of normal termination except for the fresh
			// variable that represents the result
			//////////exceptional termination for any exception that may be
			// thrown
			Formula[] wpForExcTermination = null;
			JavaObjectType[] exceptionsThrown = method.getExceptionsThrown();
			if ((exceptionsThrown != null) && (exceptionsThrown.length > 0)) {
				wpForExcTermination = new Formula[exceptionsThrown.length];
				Formula excPostOfCalledMethodForExc;
				Formula excPostOfThisMethodForExc;
				for (int s = 0; s < exceptionsThrown.length; s++) {
					excPostOfCalledMethodForExc = (Formula) method
							.getExsuresForException(exceptionsThrown[s]).copy();
					// substitute the special ExceptionVariable by a variable
					// of the same type in the exceptional
					// postcondition
					Variable excVariable = new Variable(FreshIntGenerator
							.getInt(), exceptionsThrown[s]);
					excPostOfCalledMethodForExc.substitute(
							new EXCEPTIONVariable(FreshIntGenerator.getInt(),
									exceptionsThrown[s]), excVariable);
					for (int i = 0; i < number_args; i++) {
						ArithmeticExpression counter_minus_arg_num_plus_i = (ArithmeticExpression) ArithmeticExpression
								.getArithmeticExpression(counter_minus_arg_num,
										new NumberLiteral(i),
										ExpressionConstants.SUB);
						Stack stack_at_counter_minus_arg_num_plus_i = new Stack(
								counter_minus_arg_num_plus_i);
						LocalVariable local_i = new LocalVariable(i);
						//excPost(method(index) )[ o with local(i) <-- S( t - arg_num(method(index) ) + i )]
						excPostOfCalledMethodForExc = (Formula) excPostOfCalledMethodForExc
								.substitute(local_i,
										stack_at_counter_minus_arg_num_plus_i);
					}
					excPostOfThisMethodForExc = getWpForException(
							exceptionsThrown[s], _exc_Postcondition);
					wpForExcTermination[s] = Formula.getFormula(
							excPostOfCalledMethodForExc,
							excPostOfThisMethodForExc, Connector.IMPLIES);
					/*wpForExcTermination[s] = Formula.getFormula(
							wpForExcTermination[s], quantifyOnResult);*/
					/*if ((modifiesSubst != null) && (modifies1.length > 0)) {
						for (int j = 0; j < modifies1.length; j++) {
							//rename the modified expressions by variables
							wpForExcTermination[s] = (Formula) wpForExcTermination[s]
									.rename(modifiesSubst[j], modifies1[j]);
						}
						
					}*/
				}
			}	
			if (wpForExcTermination != null) {
				Formula wpExc = Formula.getFormula(wpForExcTermination,
						Connector.AND);
				wpSpecCase = Formula.getFormula(wpSpecCase, wpExc, Connector.AND);
				
			}
			Formula modifPost = modifiesSet.getPostcondition();
			Formula nonModifPost = modifiesSet.getConditionForNonModifiedFields();
			wpSpecCase = Formula.getFormula(wpSpecCase, modifPost, Connector.AND );
			wpSpecCase = Formula.getFormula(wpSpecCase, nonModifPost, Connector.AND );
			wp_spec_cases = Formula.getFormula(wp_spec_cases, wpSpecCase, Connector.OR );
		}
		
		wp = Formula.getFormula(wp_spec_cases, requiresCalledMethod, Connector.AND );
		
		// exceptional termination
		return wp;
	}
}
