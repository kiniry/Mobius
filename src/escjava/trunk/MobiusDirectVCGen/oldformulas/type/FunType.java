package mobius.directVCGen.formula.type;

import java.util.Iterator;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.Variable;


/**
 * This class represents a functionnal type, i.e. an application of
 * several type, e.g. T1 -> T2 -> T3 -> T4 ...
 * It is implemented as a kind of linked list.
 * 
 * The general architecture is : {@link #fType} -> {@link #fFunType}.
 * 
 * @author J. Charles
 */
public class FunType implements IFormula {
	
	/** the type contained in this object */
	private final Type fType;
	
	/** the next elements of the list of types */
	private final FunType fFunType;
	
	/** 
	 * the size of the type <br/>
	 * if ({@link #fFunType} == null) then (size == 1); 
	 * if ({@link #fFunType} != null) then (size = 1 +  {@link #fFunType#size()})
	 */
	private final int fSize;
	
	/**
	 * The constructor of a functional type containing a single type.
	 * Its size is 1.
	 * @param type The type it contains
	 */
	public FunType(Type type) {
		this(type, null);
	}
	
	/**
	 * Constructor for a functional type containing at least 2 types:
	 * type -> funType...
	 * Its size is 1 +  {@link funType#size()}
	 * @param type The type contained in this element
	 * @param funType The next elements
	 */
	public FunType(Type type, FunType funType) {
		if(type == null) {
			throw new IllegalArgumentException("type == null!");
		}
		fType = type;
		fFunType = funType;
		if(funType != null) {
			fSize = funType.size() + 1;
		}
		else {
			fSize = 1;
		}
	}
	
	/**
	 * The size of the type
	 * @return a number > 0
	 */
	public int size() {
		return fSize;
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		Iterator iter = iterator();
		String res = "";
		if(!iter.hasNext()) {
			return res;
		}
		res += iter.next();
		while(iter.hasNext()) {
			res += " -> ";
			res += iter.next();
		}
		return res;
	}


	/**
	 * The type contained in this element.
	 */
	public Type getType() {
		return fType;
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#iterator()
	 */
	public Iterator<IFormula> iterator() {
		return new FTypeIterator(this);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#subst(mobius.directVCGen.formula.expression.Variable, mobius.directVCGen.formula.expression.AExpression)
	 */
	public IFormula subst(Variable var, IFormula expr) {
		return this;
	}
	
	/**
	 * An iterator to iterate over a functional type.
	 * It returns every types associated with each elements of a specific
	 * functional type.
	 * @author J. Charles
	 */
	private final static class FTypeIterator implements Iterator<IFormula> {
		/** the current element we iterate upon... */
		private FunType fFunType;
		
		/**
		 * Cronstructor of the iterator.
		 * @param funType the object on which to iterate
		 */ 
		public FTypeIterator(FunType funType) {
			fFunType = funType;
		}
		
		/*
		 * (non-Javadoc)
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {
			return fFunType.fFunType != null;
		}

		/*
		 * (non-Javadoc)
		 * @see java.util.Iterator#next()
		 */
		public IFormula next() {
			Type type = fFunType.fType;
			fFunType = fFunType.fFunType;
			return type;
		}

		/**
		 * Unsupported operation.
		 */
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitFType(this);
	}

	/**
	 * Returns the last type of the functional type. 
	 * The so-called return type.
	 * @return A valid type which is the last type available of the list
	 */
	public Type getReturnType() {
		if(fFunType != null)
			return fFunType.getReturnType();
		return getType();
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return tFunType;
	}

	public IFormula get(int index) {
		// TODO Auto-generated method stub
		return null;
	}

	public void set(int slot, IFormula f) {
		// TODO Auto-generated method stub
		
	}
}
