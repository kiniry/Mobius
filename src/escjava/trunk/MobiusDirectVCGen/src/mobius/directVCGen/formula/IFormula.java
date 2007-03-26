package mobius.directVCGen.formula;

import java.util.Iterator;

import mobius.directVCGen.formula.expression.Variable;
import mobius.directVCGen.formula.type.Type;


public interface IFormula extends Iterable<IFormula> {
	public static final int dummy = -1;
	
	public static final int pAnd = 0;
	public static final int pBoolProp = 1;
	public static final int pEquals = 2;
	public static final int pFalse = 3;
	public static final int pForAll = 4;
	public static final int pExists = 5;
	public static final int pImplies = 6;
	public static final int pNot = 7;
	public static final int pOr = 8;
	public static final int pTrue = 9;
	public static final int tFunType = 10;
	public static final int tType = 11;
	public static final int eVariable = 12;
	public static final int bAnd = 13;
	public static final int bEqualBool = 14;
	public static final int bEqualNum = 14;
	public static final int bEqualRef = 14;
	public static final int bFalse = 15;
	public static final int bImplies = 16;
	public static final int bNot = 17;
	public static final int bOr = 18;
	public static final int bTrue = 19;
	public static final int nAdd = 20;
	public static final int nGreater = 21;
	public static final int nGreaterEqual = 22;
	public static final int nLesser = 23;
	public static final int nLesserEqual = 24;
	public static final int nMinus = 25;
	public static final int nMod = 26;
	public static final int nMult = 27;
	public static final int nSub = 28;
	
	public static final int nByte = 29;
	public static final int nShort = 30;
	public static final int nInt = 31;
	public static final int nLong = 32;
	
	public Type getType ();
	public IFormula subst (Variable var, IFormula expr);
	public Iterator<IFormula> iterator();
	public void accept(IFormulaVisitor v) throws FormulaException;
	public int getID();
	
	public IFormula get(int index);
	public void set(int slot, IFormula f);
}
