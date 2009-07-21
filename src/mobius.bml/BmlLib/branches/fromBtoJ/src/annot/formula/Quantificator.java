package annot.formula;

import java.util.Vector;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;

public class Quantificator extends Expression {
	public static final String FORALL = "forall";
	public static final String EXISTS = "exists";

	private Expression[] boundVar;
	private String quantifier;
	//private Expression domain;
	
	public Quantificator(String _quantifier, Expression[] _boundVar) {
		quantifier = _quantifier;
		setBoundVars(_boundVar);
		priority = 1;
	}

	public Quantificator(
		String _quantifier,
		Expression _boundVar) {
		this(_quantifier,  new Expression[]{_boundVar});
		priority = 1;
	}

//	public void dump() {
//	}

	public Expression copy() {
		Expression[] boundVarsCopy = new Expression[boundVar.length];
		for (int i = 0; i < boundVar.length; i++) {
			boundVarsCopy[i] = boundVar[i];
		}
		Quantificator qCopy = new Quantificator(quantifier, boundVarsCopy);
		return qCopy;
	}
	
//	public boolean equals(Quantificator quantificator) {
//		if (quantificator == null) {
//			return false;
//		}
//		if (!quantificator.getQuantifier().equals(getQuantifier()) ) {
//			return false;
//		}
//		if (!equalsBound(getBoundVars()) ) {
//			return false;
//		}
///*		if (!quantificator.getDomain().equals(getDomain()) ) {
//			return false;
//		}*/
//		return true;
//	}
	
	public String printCode1(BMLConfig conf) {
		/*	if (domain == null) {*/
			String s = quantifier;
			for (int i = 0; i < boundVar.length; i++ ) {
				 s = s + " " + boundVar[i].printCode(conf);
			}
			return s + ";";
			/*return  "(" + quantifier + "  " + boundVar +  "."+ domain.toString() + ")";*/
		}

//	/**
//	 * checks if the set of quantified 
//	 * variables is equal to another 
//	 * set of variables modulo the names of the variables
//	 * @param v
//	 * @return
//	 */
//	private boolean equalsBound( Expression[] _boundVar ) {
//		// if the lists donot havethe same length they are not equal
//		if (boundVar.length !=  _boundVar.length) {
//			return false;
//		}
//		Vector  notFound = new Vector();
//		Vector  _notFound = new Vector();
//		for (int i = 0; i < boundVar.length; i++) {
//			notFound.add(boundVar[i].getType());
//			_notFound.add(_boundVar[i].getType());
//			
//		}
//		// tests if for every bound variable in boundVar there is a variable 
//		// in _boundVar with the same type
//		while (notFound.isEmpty() ) { 
//			JavaType type = (JavaType)notFound.get(0);
//			int i = 0;
//			for (i = 0; i < _notFound.size(); i++) { 
//				if ( type != (JavaType)_notFound.elementAt(i)  ) {
//					continue;
//				} else {
//					break;
//				}
//			}
//			if ( i > _notFound.size() ) {
//				break ;
//			}
//			notFound.remove(0);
//			_notFound.remove( i);
//		}
//		if ( notFound.isEmpty() && _notFound.isEmpty()) {
//			return true;
//		}
//		return false;
//	}
//	
//	/**
//	 * @return
//	 */
//	public Expression[] getBoundVars() {
//		return boundVar;
//	}

	/**
	 * @param expression
	 */
	public void setBoundVars(Expression[] expression) {
		boundVar = expression;
	}

//	 
//	public Expression substitute(Expression _e1, Expression _e2) {
//	
//		return this;
//	}
//
///*	*//**
//	 * @return Returns the domain.
//	 *//*
//	public Expression getDomain() {
//		return domain;
//	}*/
//	/**
//	 * @return Returns the quantifier.
//	 */
//	public String getQuantifier() {
//		return quantifier;
//	}
}
