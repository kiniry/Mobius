/*
 * Created on Jun 30, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.objectmanipulation;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_to_JPO.B2JPackage;
import bytecode_wp.bc.io.ReadAttributeException;
import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcclass.BCConstantPool;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcclass.attributes.MethodSpecification;
import bytecode_wp.bcclass.attributes.SpecificationCase;
import bytecode_wp.bcclass.utils.MethodSignature;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.EXCEPTIONVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.Variable;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.RESULT;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.block.IllegalLoopException;
import bytecode_wp.constants.BCConstantClass;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.constants.BCConstantMethodRef;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;

import bytecode_wp.modifexpression.Everything;
import bytecode_wp.modifexpression.ModifiesExpression;
import bytecode_wp.utils.FreshIntGenerator;

import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;

/**
 * the method models a method invokation.
 * 
 * @author mpavlova
 */
public class BCInvoke extends BCFieldOrMethodInstruction {

	// the invoked method
	private BCMethod method = null;

	/**
	 * @param _instruction
	 * @param _type
	 * @param _classType
	 * @param _cp - the constant pool of the class where this invocation is done 
	 */
	public BCInvoke(InstructionHandle _instruction, JavaType _type,
			JavaType _classType, BCConstantPool _cp) {
		super(_instruction, _type, _classType, _cp);
	}

	public BCMethod getInvokedMethod(IJml2bConfiguration config)
			throws IllegalLoopException {
		if (method != null) {
			return method;
		}
		BCConstantMethodRef method_constant = (BCConstantMethodRef) (getConstantPool()
				.getConstant(getIndex()));
		String clazz_name = ((BCConstantClass) (getConstantPool()
				.getConstant(method_constant.getClassIndex()))).getName();
		// find the class where the called method is declared
		BCClass clazz = ((B2JPackage) config.getPackage()).getClass(clazz_name);
		

		clazz.setConfig(config);
		// get the method instance
		

		try {
			String signature = MethodSignature.getSignature(method_constant
					.getName(), method_constant.getSignature());
			method = clazz.lookupMethod(config, signature);
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}

		return method;
	}

	/**
	 * 
	 * @param config
	 * @return the number of the elements starting from the stack top that are
	 *         arguments of the invoked method
	 */
	private int getArgumentsOnStack(IJml2bConfiguration config) {
		try {
			method = getInvokedMethod(config);
		} catch (IllegalLoopException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		int instance_number_args = 0;
		if (!(this instanceof BCINVOKESTATIC)) {
			// if the method is an instance method ( not static )
			instance_number_args = method.getNumberArguments() + 1;
		} else {
			instance_number_args = method.getNumberArguments();
		}
		return instance_number_args;

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula,
	 *      specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
	
		return null;
	}

	private VCGPath getModifiesCondition(VCGPath postcondition,
			ModifiesExpression[] modifiesSubst, IJml2bConfiguration config) {
		
		for (int i = 0; i < modifiesSubst.length; i++) {
			if (modifiesSubst[i] == null) {
				continue;
			}
			Formula f = (Formula) modifiesSubst[i].getPostCondition(config,
					getPosition());
			Integer hypKey = postcondition.addHyp(getPosition(), f);
			postcondition.addHypsToVCs(hypKey);

		}
		return postcondition;
	}

	/**
	 * the method quantifies the locations that are modified by the called
	 * method in the predicates that must hold after the method call
	 * 
	 * @param postcondition
	 *            of the called method
	 * @param modifies
	 *            the locations that are modified by the invoked method
	 * @return
	 */
	private Expression initModifiesLocations(Expression postcondition,
			ModifiesExpression[] modifies, IJml2bConfiguration config) {

		if (modifies == null) {
			return postcondition;
		}
		//  if the called method may modify any location then freeze all locations 
		if ( modifies[0] instanceof Everything) {
			postcondition.atState(getPosition());
			return postcondition;
		} 
		for (int i = 0; i < modifies.length; i++) {
			if (modifies[i] == null) {
				continue;
			}
			BCConstantFieldRef fieldRef = (BCConstantFieldRef) modifies[i]
					.getExpressionModifies();
			postcondition.atState(getPosition(), fieldRef);
		}
		return postcondition;
	}

	private Formula substituteLocVarWithStackElem(Formula postcondition,
			IJml2bConfiguration config) {
		if (Predicate0Ar.TRUE == postcondition) {
			return postcondition;
		}
		// le nombre des arguments 
		int instance_number_args = getArgumentsOnStack(config);
		ArithmeticExpression counter_minus_arg_num = (ArithmeticExpression) ArithmeticExpression
				.getArithmeticExpression(Expression.COUNTER, new NumberLiteral(
						instance_number_args - 1), ExpressionConstants.SUB);
		for (int i = 0; i < instance_number_args; i++) {
			ArithmeticExpression counter_minus_arg_num_plus_i = (ArithmeticExpression) ArithmeticExpression
					.getArithmeticExpression(counter_minus_arg_num.copy(),
							new NumberLiteral(i), ExpressionConstants.ADD);
			Stack stack_at_counter_minus_arg_num_plus_i = new Stack(
					counter_minus_arg_num_plus_i);
			BCLocalVariable local_i = method.getLocalVariableAtIndex(i);

			postcondition = (Formula) postcondition.substitute(local_i,
					stack_at_counter_minus_arg_num_plus_i);
			/*
			 * if (modifiesSubst != null) { for (int m = 0; m <
			 * modifiesSubst.length; m++) { if (modifiesSubst[m] == null) {
			 * continue; } modifiesSubst[m] = (ModifiesExpression)
			 * modifiesSubst[m] .substitute(local_i,
			 * stack_at_counter_minus_arg_num_plus_i); } }
			 */
		}
		return postcondition;
	}

	/**
	 * this method sets the modified expression of the called method to their
	 * proper values in the state when the method is called
	 * 
	 */
	private ModifiesExpression[] initModifies(ModifiesExpression[] modifies,
			IJml2bConfiguration config) {
		ModifiesExpression[] modifiesSubst = new ModifiesExpression[modifies.length];

		for (int i = 0; i < modifies.length; i++) {
			modifiesSubst[i] = (ModifiesExpression) modifies[i].copy();
		}
		int instance_number_args = getArgumentsOnStack(config);
		ArithmeticExpression counter_minus_arg_num = (ArithmeticExpression) ArithmeticExpression
				.getArithmeticExpression(Expression.COUNTER, new NumberLiteral(
						instance_number_args - 1), ExpressionConstants.SUB);
		for (int i = 0; i < instance_number_args; i++) {
			ArithmeticExpression counter_minus_arg_num_plus_i = (ArithmeticExpression) ArithmeticExpression
					.getArithmeticExpression(counter_minus_arg_num,
							new NumberLiteral(i), ExpressionConstants.ADD);
			Stack stack_at_counter_minus_arg_num_plus_i = new Stack(
					counter_minus_arg_num_plus_i);
			BCLocalVariable local_i = method.getLocalVariableAtIndex(i);

			
			if (modifiesSubst != null) {
				for (int m = 0; m < modifiesSubst.length; m++) {
					if (modifiesSubst[m] == null) {
						continue;
					}
					modifiesSubst[m] = (ModifiesExpression) modifiesSubst[m]
							.substitute(local_i,
									stack_at_counter_minus_arg_num_plus_i);
				}
			}
		}
		return modifiesSubst;
	}

	private void addHypCalleeNotNull(VCGPath _normalPostcondition) {
		if (this instanceof BCINVOKESTATIC) {
			return;
		}
		int top_minus_number_args_minus_obj_plus_res;
		/*if (method.getReturnType() == JavaType.JavaVOID) {
			
			top_minus_number_args_minus_obj_plus_res = method
					.getNumberArguments() + 1;// instance_number_args + 1;
		} else {
			top_minus_number_args_minus_obj_plus_res = method
					.getNumberArguments();
		}*/
		top_minus_number_args_minus_obj_plus_res = method
		.getNumberArguments();
		Formula calleeDiffNull = Formula.getFormula(new Predicate2Ar(new Stack(
				ArithmeticExpression.getArithmeticExpression(
						Expression.COUNTER, new NumberLiteral(
								top_minus_number_args_minus_obj_plus_res),
						ExpressionConstants.SUB)), Expression._NULL,
				PredicateSymbol.EQ), Connector.NOT);
		// hypthese that the callee is not null
		Integer key = _normalPostcondition
				.addHyp(getPosition(), calleeDiffNull);
		_normalPostcondition.addHypsToVCs(key);
	}

	public VCGPath wp(IJml2bConfiguration config,
			VCGPath _normal_Postcondition, ExsuresTable _exc) {
		
		try {
			method = getInvokedMethod(config);
		} catch (IllegalLoopException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		// /////////////////////////////////////////////////
		// Normal case /////////////////////////////////////
		// ///////////////////////////////////////////////////////////
		// ///////////////////////////////////////////////////////////////////

		MethodSpecification methodSpecification = method
				.getMethodSpecification();
		Formula requiresCalledMethod = null;
		Formula invariant;
		SpecificationCase[] specCases = null;

		if (methodSpecification == null) {
			requiresCalledMethod = Predicate0Ar.TRUE;
			invariant = Predicate0Ar.TRUE;
		} else {
			// get the precondition of the method
			requiresCalledMethod = (Formula) methodSpecification
					.getDesugaredPrecondition().copy();
			invariant = (method.isInit()) ? methodSpecification
					.getInvariantAfterInit() : methodSpecification
					.getInvariant();
			specCases = methodSpecification.getSpecificationCases();
		}

		// how much elements are taken from the stack top
		int instance_number_args = getArgumentsOnStack(config);

		requiresCalledMethod = substituteLocVarWithStackElem(
				requiresCalledMethod, config);

	
		Variable fresh_result = null;
		int top_minus_number_args_minus_obj_plus_res;
		if (!(this instanceof BCINVOKESTATIC)) {
			if (method.getReturnType() == JavaType.JavaVOID) {
				top_minus_number_args_minus_obj_plus_res = method
						.getNumberArguments() + 1;// instance_number_args + 1;
			} else {
				top_minus_number_args_minus_obj_plus_res = method
						.getNumberArguments();
				
				fresh_result = new Variable(FreshIntGenerator.getInt(), method
						.getReturnType());
			}

		} else {
			if (method.getReturnType() == JavaType.JavaVOID) {
				top_minus_number_args_minus_obj_plus_res = method.getNumberArguments();
			} else {
				top_minus_number_args_minus_obj_plus_res = method
						.getNumberArguments() - 1;
			
				fresh_result = new Variable(FreshIntGenerator.getInt(), method
						.getReturnType());
			}
		}

		ArithmeticExpression counter_minus_arg_num_plus_1 = (ArithmeticExpression) ArithmeticExpression
				.getArithmeticExpression(Expression.COUNTER, new NumberLiteral(
						top_minus_number_args_minus_obj_plus_res),
						ExpressionConstants.SUB);
		// psi^n[t <-- t - arg_n_plus_1 ]
		// /// substitute in the postcondition of the invokation the top of the
		// stack with the result that the
		// // invoked method returns
		_normal_Postcondition.substitute(Expression.COUNTER,
				counter_minus_arg_num_plus_1);

		// psi^n[ S(t ) <-- fresh]
		if (fresh_result != null) {
			_normal_Postcondition.substitute(new Stack(
					counter_minus_arg_num_plus_1), fresh_result);
		}
		if (specCases == null) {
			/*
			 * wp = Formula.getFormula(requiresCalledMethod,
			 * _normal_Postcondition, Connector.AND);
			 */

			_normal_Postcondition.addGoal(VcType.PRE_METH_CALL,
					requiresCalledMethod);
			_normal_Postcondition.addGoal(VcType.INSTANCE_INVARIANT,
					invariant);
			return _normal_Postcondition;
		}
		for (int specIndex = 0; specIndex < specCases.length; specIndex++) {
			Formula postcondition = (Formula) specCases[specIndex]
					.getPostcondition().copy();
			  
			Expression quantifyOnResult = null;

			// post(method(index) )[result <-- fresh ]
			if (method.getReturnType() != JavaType.JavaVOID) {
				RESULT result = Expression._RESULT;
				postcondition = (Formula) postcondition.substitute(result,
						fresh_result);
			//TODO - commented on 06/10 due to bad subtyping 
			/*	if ( method.getReturnType() instanceof JavaObjectType) {
					quantifyOnResult = new Predicate2Ar(new TYPEOF( fresh_result ), method
							.getReturnType(), PredicateSymbol.SUBTYPE);
				} else { // the return type is a basic type
					quantifyOnResult = new Variable( fresh_result , method.getReturnType()); ******************************* 
				}*/
			}
			// substitute all the local variables in the precondition, the
			// postcondition
			// and the expressions in the modifies clause of the called method
			// with the values that are in the stack .
			// do these substitutions :
			// local(0) <-- S( t - arg_num(method(index) ) + 0),
			// local(1) <-- S( t - arg_num(method(index) ) + 1),
			// local(i) <-- S( t - arg_num(method(index) ) + i)
			/* ModifiesSet modifiesSet = specCases[n].getModifies(); */
			ModifiesExpression[] modifies = specCases[specIndex].getModifies()
					.getModifiesExpressions();

			/*
			 * ModifiesSet modifiesSetSubst = new ModifiesSet(modifiesSubst,
			 * specCases[n].getModifies().getConstantPool());
			 */
			ModifiesExpression[] modifiesSubst = initModifies(modifies, config);
			postcondition = (Formula) initModifiesLocations(postcondition,
					modifiesSubst, config);
			postcondition = (Formula) postcondition.removeOLD();
			postcondition = substituteLocVarWithStackElem(postcondition, config);
			_normal_Postcondition = (VCGPath) initModifiesLocations(
					_normal_Postcondition, modifiesSubst, config);

			// add the hypothesis about the nonmodified locations
			_normal_Postcondition = getModifiesCondition(_normal_Postcondition,
					modifiesSubst, config);

			// ADD them as hypothesis

			Integer keyMethCallPost = _normal_Postcondition.addHyp(
					getPosition(), postcondition);
			_normal_Postcondition.addHypsToVCs(keyMethCallPost);
			// add the condition about the result variable
			
	///////////// commented on 06/10/05 because of a bug in the proof obligations : 
	//////////// a bug due to bad subtyping		
/*			if (quantifyOnResult != null) {
				Integer keyResType = _normal_Postcondition.addHyp(
						getPosition(), quantifyOnResult);
				_normal_Postcondition.addHypsToVCs(keyResType);
			}*/
			addHypCalleeNotNull(_normal_Postcondition);
		
			// //////////////////////////////////////////////////////
			// //////////////////////Exceptional Termination////////
			// /////////////////////////////////////////////
			// //////////////////////////////////////////////////////
			// one must quantify the exceptional behaviour
			// for all (modifies ) (excPost(index, exc) ==> psi^exc(exc)) ,
			// then quantify over the same the expression
			// as in the case of normal termination except for the fresh
			// variable that represents the result
			// exceptional termination for any exception that may be
			// thrown
			VCGPath allexcPostOfThisMethodForExc = null;
			JavaObjectType[] exceptionsThrown = method.getExceptionsThrown();
			if ((exceptionsThrown != null) && (exceptionsThrown.length > 0)) {
				Formula excPostOfCalledMethodForExc = null;

				// find the exceptions that the called may throw
				for (int s = 0; s < exceptionsThrown.length; s++) {
					VCGPath excPostOfThisMethodForExc;
					excPostOfCalledMethodForExc = (Formula) method
							.getExsuresForExceptionOnCall(exceptionsThrown[s]).copy();

					// guard this exceptional postcondition by the precondition
					// of the current specification case

					// substitute the special ExceptionVariable by a variable
					// of the same type in the exceptional
					// postcondition
					Variable excVariable = new Variable(FreshIntGenerator
							.getInt(), exceptionsThrown[s]);
					excPostOfCalledMethodForExc.substitute(
							new EXCEPTIONVariable(FreshIntGenerator.getInt(),
									exceptionsThrown[s]), excVariable);
					ArithmeticExpression counter_minus_arg_num = (ArithmeticExpression) ArithmeticExpression
							.getArithmeticExpression(
									Expression.COUNTER,
									new NumberLiteral(instance_number_args - 1),
									ExpressionConstants.SUB);
					for (int i = 0; i < instance_number_args; i++) {
						ArithmeticExpression counter_minus_arg_num_plus_i = (ArithmeticExpression) ArithmeticExpression
								.getArithmeticExpression(counter_minus_arg_num,
										new NumberLiteral(i),
										ExpressionConstants.SUB);
						Stack stack_at_counter_minus_arg_num_plus_i = new Stack(
								counter_minus_arg_num_plus_i);
						BCLocalVariable local_i = method
								.getLocalVariableAtIndex(i);
						// excPost(method(index) )[ o with local(i) <-- S( t -
						// arg_num(method(index) ) + i )]
						excPostOfCalledMethodForExc = (Formula) excPostOfCalledMethodForExc
								.substitute(local_i,
										stack_at_counter_minus_arg_num_plus_i);
					}
					excPostOfThisMethodForExc = getWpForException(config,
							exceptionsThrown[s]);
					// add as hypothesis the exceptional postcondition of the
					// called method
					Integer methExcPostKey = excPostOfThisMethodForExc.addHyp(
							getPosition(), excPostOfCalledMethodForExc);
					excPostOfThisMethodForExc.addHypsToVCs(methExcPostKey);

					if (allexcPostOfThisMethodForExc == null) {
						allexcPostOfThisMethodForExc = excPostOfThisMethodForExc;
					} else {
						allexcPostOfThisMethodForExc
								.merge(excPostOfThisMethodForExc);
						excPostOfCalledMethodForExc = null;
					}
					/*
					 * wpForExcTermination[s] = Formula.getFormula(
					 * excPostOfCalledMethodForExc, excPostOfThisMethodForExc,
					 * Connector.IMPLIES);
					 */

				}
				if (allexcPostOfThisMethodForExc != null) {
					// make a conjunction of the possible exceptional
					// termination postconditions

					_normal_Postcondition.merge(allexcPostOfThisMethodForExc);
					allexcPostOfThisMethodForExc = null;
				}
			}

			// exceptional termination
		}
		_normal_Postcondition.addGoal(VcType.PRE_METH_CALL,
				requiresCalledMethod);
		_normal_Postcondition.addGoal(VcType.INSTANCE_INVARIANT,
				invariant);
		/* wp = (Formula) Formula.getFormula(getAssert(), wp, Connector.AND); */
		return _normal_Postcondition;

	}
}