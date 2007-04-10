package mobius.directVCGen.formula;

import java.util.Iterator;

import mobius.directVCGen.formula.expression.Variable;
import mobius.directVCGen.formula.type.Type;

/**
 * The classes implementing this interface represent formulas.
 * A formula is associated with an ID, an integer which defines its type.
 * People can also use visitor patterns to go through formulas.
 * @author J. Charles
 */
public interface IFormula extends Iterable<IFormula> {
	/** the ID used for the dummy formula, 0 */
	public static final int dummy = 0;
	
	/** the ID used for the type {@link mobius.directVCGen.formula.type.FunType} */
	public static final int tFunType = 	1;
	/** the ID used for the type {@link mobius.directVCGen.formula.type.Type} */
	public static final int tType = 	2;
	
	public static final int pAnd = 		101;
	public static final int pBoolProp = 102;
	public static final int pEquals = 	103;
	public static final int pFalse = 	104;
	public static final int pForAll = 	105;
	public static final int pExists = 	106;
	public static final int pImplies = 	107;
	public static final int pNot = 		108;
	public static final int pOr = 		109;
	public static final int pTrue = 	110;
	
	public static final int eVariable = 21;
	
	public static final int bAnd = 			301;
	public static final int bEqualBool = 	302;
	public static final int bEqualNum = 	303;
	public static final int bEqualRef = 	304;
	public static final int bFalse = 		305;
	public static final int bImplies = 		306;
	public static final int bNot = 			307;
	public static final int bOr = 			308;
	public static final int bTrue = 		309;

	public static final int bGreaterN = 	310;
	public static final int bGreaterEqN = 	311;
	public static final int bLesserN = 		312;
	public static final int bLesserEqN = 	313;
	
	public static final int nAdd =		40;
	public static final int nMinus = 	41;
	public static final int nMod = 		42;
	public static final int nMult = 	43;
	public static final int nSub = 		44;
	
	public static final int nByte = 	45;
	public static final int nShort = 	46;
	public static final int nInt = 		47;
	public static final int nLong = 	48;
	
	public static final int fFloat = 	50;
	public static final int fDouble = 	51;
	
	public static final int fAdd = 		52;
	public static final int fMinus = 	53;
	public static final int fMult = 	54;
	public static final int fSub = 		55;
	
	public static final int rNull = 	60;
	/**
	 * Return the type of the formula.
	 * @return the type of the formula; cannot be null.
	 */
	public Type getType ();
	
	/**
	 * Substitute the variable with the given expression. 
	 * If the substitution has no effect it returns the the current
	 * object, otherwise it returns a new instance. 
	 * @param var the variable to substitute
	 * @param expr the expression to replace the variable with
	 * @return a new object modified by the substitution or <code>this</code>
	 */
	public IFormula subst (Variable var, IFormula expr);
	
	/**
	 * Return an iterator over the children of the formula, i.e.
	 * each element of the iterator has the type {@link mobius.directVCGen.formula.IFormula}
	 */
	public Iterator<IFormula> iterator();
	
	/**
	 * The method accept of the Visitor design pattern...
	 * @param v the visitor to make visit the formula
	 * @throws FormulaException if there is an error the visit methods
	 * should throw an exception of this type.
	 */
	public void accept(IFormulaVisitor v) throws FormulaException;
	
	/**
	 * It gives the ID of the formula, the type of the formula as
	 * a form of integer. The different possible IDs are the static
	 * fields of the interface {@link mobius.directVCGen.formula.IFormula}
	 * The IDs are defined statically in this interface for ease of use. 
	 * But custom IDs can be used (not recommended, of course).
	 * @return a valid ID 
	 */
	public int getID();
	
	/**
	 * Returns the child at the given index.
	 * @param index the index of the child to return
	 * @return the child specified by the index
	 */
	public IFormula get(int index);
	
	/**
	 * Replace the child with the given formula. 
	 * @param slot the index where to put the formula
	 * @param f the formula to put as a child
	 */
	public void set(int slot, IFormula f);
	
	/**
	 * Returns the number of children of the current formula.
	 */
	public int size();
}
