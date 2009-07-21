/*
 * Created on Apr 24, 2005
 * */
package annot.bcexpression;

import annot.bcclass.BMLConfig;
import annot.constants.BCConstantMethodRef;
import annot.formula.Formula;


/**
 * @author M.Pavlova
 * 
 * this class represents a method call to a pure method
 */
public class MethodInvocation extends Expression {
    private BCConstantMethodRef methodReference;

    private Variable result;

    private Formula precondition;

    
    private Formula[] specCases;

    /**
     * the subexpression list contains
     * <ol>
     * <li><>the first element in the list is a reference on which the method
     * call is done. If it is <em>null</em> this means that the class is
     * static</li>
     * <li>the rest of the elements are the effective arguments passed to
     * method call</li>
     * </ol>
     * 
     * @param subExpr
     */
    public MethodInvocation( BCConstantMethodRef cpMethRef,
            Expression[] subExpr) {
        super(subExpr);
        methodReference = cpMethRef;

    }

//    /**
//     * the method sets the variable result if it is not void
//     *  
//     */
//    private void setResult() {
//        if (methodReference.getReturnType() == JavaType.JavaVOID) {
//            result = null;
//        }
//        result = new Variable(FreshIntGenerator.getInt(), methodReference
//                .getReturnType());
//    }
//
//    private void setSpecification(IJml2bConfiguration config) throws ReadAttributeException,
//            IllegalLoopException {
//    	String clazzName = methodReference.getClassWhereDeclared().getSignature();
//        BCClass clazz = ((B2JPackage) config.getPackage()).getClass(clazzName);
//        String signature = MethodSignature.getSignature(methodReference
//                .getName(), methodReference.getSignature());
//        BCMethod method = clazz.lookupMethod(config, signature);
//        MethodSpecification spec = method.getMethodSpecification();
//        SpecificationCase[] _specCases = spec.getSpecificationCases();
//        if (_specCases == null) {
//        	precondition = spec.getDesugaredPrecondition();
//        	return;
//        }
///*        for (int i = 0 ; i <= _specCases.length; i++ ) {
//        	Formula pre = _specCases[i].getPrecondition();
//        	Formula post = _specCases[i].getPostcondition();
//        	specCases = Formula.getFormula(pre, post, Connect )
//        } 
//        	*/
//    }
//
//
//
//
//    /**
//     * 
//     * @return the list of arguments of the method call
//     */
//    public Expression[] getArguments() {
//        if (getSubExpressions() == null) {
//            return null;
//        }
//        // no arguments
//        if (getSubExpressions().length <= 1) {
//            return null;
//        }
//        Expression[] subExpr = getSubExpressions();
//        if (subExpr == null) {
//        	return null;
//        }
//        Expression[] args = new Expression[ subExpr.length];
//        for (int i = 1; i < subExpr.length; i++) {
//            args[i - 1] = subExpr[i];
//        }
//        return args;
//    }
//
//    /*
//     * (non-Javadoc)
//     * 
//     * @see bytecode_wp.bcexpression.Expression#substitute(bytecode_wp.bcexpression.Expression,
//     *      bytecode_wp.bcexpression.Expression)
//     */
//    public Expression substitute(Expression _e1, Expression _e2) {
//        if (getSubExpressions() == null) {
//            return this;
//        }
//        Expression[] subExpr = getSubExpressions();
//
//        for (int i = 1; i < subExpr.length; i++) {
//            subExpr[i] = subExpr[i].substitute(_e1, _e2);
//        }
//        return this;
//    }
//
//    /*
//     * (non-Javadoc)
//     * 
//     * @see bytecode_wp.bcexpression.Expression#toString()
//     */
    public String printCode1(BMLConfig conf) {
        return result.printCode1(conf);
    }

    /**
     * @return a deep copy of the object
     * 
     * @see bytecode_wp.bcexpression.Expression#copy()
     */
    public Expression copy() {
//    	String clazzName = methodReference.getClassWhereDeclared().getSignature();
        if (getSubExpressions() == null) {
            //the method is static; null stands for
            // the instance upon which the method is called
            Expression[] subExprCopy = new Expression[] { null };
            return new MethodInvocation( methodReference, subExprCopy);
        }
        Expression[] subExpr = getSubExpressions();
        Expression[] subExprCopy = new Expression[subExpr.length];
        for (int i = 1; i < subExpr.length; i++) {
            subExprCopy[i] = subExpr[i].copy();
        }
        MethodInvocation methInvCopy = new MethodInvocation(methodReference, subExprCopy);
        return methInvCopy;
    }

}
