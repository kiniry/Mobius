package mobius.directVCGen.formula.type;

import java.util.Iterator;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.Variable;


/**
 * A class made to represent types.
 * @author J. Charles
 */
public class Type implements IFormula{
	/** the boolean type */
	public static final Type bool = new Type("bool"); 	
	
	/** the reference type */
	public static final Type refs = new Type("reference"); 

	/** the numeric type */
	public static final Type num = new NumType("num"); 
	
	/** the integer type */
	public static final Type numInt = new NumType("int"); 
	
	/** the byte type */
	public static final Type numByte = new NumType("byte"); 
	
	/** the short type */
	public static final Type numShort = new NumType("short"); 
	
	/** the long type */
	public static final Type numLong = new NumType("long"); 
	
	/** the prop type */
	public static final Type prop = new Type("Property");
	
	/** the type type */
	public static final Type type = new Type("Type");
	
	/** the undefined type */
	public static final Type undef = new Type("Undef");
	
	/** a string description of the type */
	private String fDesc;

	/** a constructor */
	protected Type(String desc) {
		fDesc = desc;
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	public boolean equals(Object o) {
		return (o instanceof Type) && o.hashCode() == this.hashCode();
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	public int hashCode() {
		return fDesc.hashCode();
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return fDesc;
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getType()
	 */
	public Type getType() {
		return Type.type;
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#subst(mobius.directVCGen.formula.expression.Variable, mobius.directVCGen.formula.expression.AExpression)
	 */
	public IFormula subst(Variable var, IFormula expr) {
		return this;
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#iterator()
	 */
	public Iterator<IFormula> iterator() {
		return new EmptyFormulaIterator();
	}
	
	/**
	 * Empty iterator... does no thing.
	 * @author J. Charles
	 */
	public static class EmptyFormulaIterator implements Iterator<IFormula> {
		/*
		 * (non-Javadoc)
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {
			return false;
		}
		
		/*
		 * (non-Javadoc)
		 * @see java.util.Iterator#next()
		 */
		public IFormula next() {
			return null;
		}
		/*
		 * (non-Javadoc)
		 * @see java.util.Iterator#remove()
		 */
		public void remove() {
		}
		
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitType(this);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return tType;
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#get(int)
	 */
	public IFormula get(int index) {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#set(int, mobius.directVCGen.formula.IFormula)
	 */
	public void set(int slot, IFormula f) {
		
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#size()
	 */
	public int size() {
		return 0;
	}
}
