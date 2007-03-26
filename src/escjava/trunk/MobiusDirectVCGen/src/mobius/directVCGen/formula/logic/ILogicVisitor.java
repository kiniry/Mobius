package mobius.directVCGen.formula.logic;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.IExpressionVisitor;

/**
 * This interface is made to contain all the methods to visit 
 * all logical constructs. 
 * Visitor classes should not implement this interface directly but 
 * rather the {@link mobius.directVCGen.formula.IFormulaVisitor} interface.
 * @author J. Charles
 */
public interface ILogicVisitor extends IExpressionVisitor {
	/**
	 * Visit an And construct.
	 * @param a the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitAnd(And a) throws FormulaException;
	
	/**
	 * Visit Equals construct.
	 * @param e the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitEquals(Equals e) throws FormulaException;
	
	/**
	 * Visit a False construct.
	 * @param f the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitFalse(False f) throws FormulaException;
	
	/**
	 * Visit a ForAll construct.
	 * @param f the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitForAll(ForAll f) throws FormulaException;

	/**
	 * Visit an Exists construct.
	 * @param f the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitExists(Exists f) throws FormulaException;
	
	/**
	 * Visit the Implies construct.
	 * @param i the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitImplies(Implies i) throws FormulaException;
	
	/**
	 * Visit the Or construct.
	 * @param o the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitOr(Or o) throws FormulaException;
	
	/**
	 * Visit the True construct.
	 * @param i the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitTrue(True i) throws FormulaException;
	
	/**
	 * Visit the BoolProp construct.
	 * @param bp the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitBoolProp(BoolProp bp) throws FormulaException;	
	
	/**
	 * Visit the Not construct.
	 * @param n the construct to inspect
	 * @throws FormulaException in case of error the user can throw 
	 * this exception.
	 */
	public void visitNot(Not n) throws FormulaException;
}
