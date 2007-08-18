package annot.formula;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;

public class Predicate2Ar extends Predicate {
//	public static final boolean SIMPLIFY_PRED = true;

	public Predicate2Ar(Expression _term1, Expression _term2,
			byte _predicateSymbol) {
		super(_term1, _term2, _predicateSymbol);
		setPriority();
	}

	private void setPriority() {
		byte ps = getPredicateSymbol();
		switch (ps) {
		case PredicateSymbol.EQ: priority = 7; break;
		case PredicateSymbol.NOTEQ: priority = 7; break;
		case PredicateSymbol.GRT: priority = 6; break;
		case PredicateSymbol.GRT_uscmp: priority = 6; break;
		case PredicateSymbol.GRTEQ: priority = 6; break;
		case PredicateSymbol.GRTEQ_uscmp: priority = 6; break;
		case PredicateSymbol.LESS: priority = 6; break;
		case PredicateSymbol.LESS_uscmp: priority = 6; break;
		case PredicateSymbol.LESSEQ: priority = 6; break;
		case PredicateSymbol.LESSEQ_uscmp: priority = 6; break;
		case PredicateSymbol.INSTANCEOF: priority = 6; break;
		case PredicateSymbol.ODD: priority = 6; break; // co to jest?
		case PredicateSymbol.SUBTYPE: priority = 1; break; //?
		default:
			System.err.println("ERROR (Predicate2Ar.setPriority: unknown predicate symbol");
		}
	}
	
	public String printRoot(BMLConfig conf) {
		byte ps = getPredicateSymbol();
		switch (ps) {
		case PredicateSymbol.EQ: return " == ";
		case PredicateSymbol.NOTEQ: return " != ";
		case PredicateSymbol.GRT: return " > ";
		case PredicateSymbol.GRT_uscmp: return " >_cmp ";
		case PredicateSymbol.GRTEQ: return " >= ";
		case PredicateSymbol.GRTEQ_uscmp: return " >=_cmp ";
		case PredicateSymbol.LESS: return " < ";
		case PredicateSymbol.LESS_uscmp: return " <_cmp ";
		case PredicateSymbol.LESSEQ: return " <= ";
		case PredicateSymbol.LESSEQ_uscmp: return " <=_cmp ";
		case PredicateSymbol.INSTANCEOF: return " instanceof ";
		case PredicateSymbol.ODD: return " odd ";
		case PredicateSymbol.SUBTYPE: return " <: ";
		default: return "?";
		}
	}

	
	public Expression getLeftExpr() {
		return getSubExpressions()[0];
	}

	public Expression getRightExpr() {
		return getSubExpressions()[1];
	}

//	public void setLeftExpr(Expression left) {
//		Expression[] expr = getSubExpressions();
//		expr[0] = left;
//	}
//
//	public void setRightExpr(Expression right) {
//		Expression[] expr = getSubExpressions();
//		expr[1] = right;
//	}

	public static Predicate getPredicate(Expression _term1, Expression _term2,
			byte _predicateSymbol) {
		Predicate p = null;
//		if (SIMPLIFY_PRED) {
//			if (_predicateSymbol == PredicateSymbol.EQ) {
//				p = simplifyEQUALS(_term1, _term2);
//			}
//
//			if ((_predicateSymbol == PredicateSymbol.GRT)
//					|| (_predicateSymbol == PredicateSymbol.GRTEQ)
//					|| (_predicateSymbol == PredicateSymbol.LESS)
//					|| (_predicateSymbol == PredicateSymbol.LESSEQ)) {
//				p = simplifyNUMBERRELATION(_term1, _term2, _predicateSymbol);
//			}
//			return p;
//		}
		return new Predicate2Ar(_term1, _term2, _predicateSymbol);
	}

//	public static Predicate simplifyNUMBERRELATION(Expression _term1,
//			Expression _term2, byte _predicateSymbol) {
//		Predicate p = null;
//		if (!(_term1 instanceof NumberLiteral)
//				|| !(_term2 instanceof NumberLiteral)) {
//			p = new Predicate2Ar(_term1, _term2, _predicateSymbol);
//			return p;
//		}
//
//		// the two terms are number literals
//		int value1 = ((NumberLiteral) _term1).getLiteral();
//		int value2 = ((NumberLiteral) _term2).getLiteral();
//		if (_predicateSymbol == PredicateSymbol.EQ) {
//			if (value1 == value2) {
//				return Predicate0Ar.TRUE;
//			} else {
//				return Predicate0Ar.FALSE;
//			}
//		} else if (_predicateSymbol == PredicateSymbol.GRT) {
//			if (value1 > value2) {
//				return Predicate0Ar.TRUE;
//			} else {
//				return Predicate0Ar.FALSE;
//			}
//		} else if (_predicateSymbol == PredicateSymbol.GRTEQ) {
//			if (value1 >= value2) {
//				return Predicate0Ar.TRUE;
//			} else {
//				return Predicate0Ar.FALSE;
//			}
//		} else if (_predicateSymbol == PredicateSymbol.LESS) {
//			if (value1 < value2) {
//				return Predicate0Ar.TRUE;
//			} else {
//				return Predicate0Ar.FALSE;
//			}
//
//		} else if (_predicateSymbol == PredicateSymbol.LESSEQ) {
//			if (value1 <= value2) {
//				return Predicate0Ar.TRUE;
//			} else {
//				return Predicate0Ar.FALSE;
//			}
//		}
//		return new Predicate2Ar(_term1, _term2, _predicateSymbol);
//	}
//
//	private static Predicate simplifyEQUALS(Expression _term1, Expression _term2) {
//		if (_term1.equals(_term2)) {
//			return Predicate0Ar.TRUE;
//		}
//		if ((_term1 == Predicate0Ar.TRUE) && (_term2 == Predicate0Ar.FALSE)) {
//			return Predicate0Ar.FALSE;
//		}
//		if ((_term2 == Predicate0Ar.TRUE) && (_term1 == Predicate0Ar.FALSE)) {
//			return Predicate0Ar.FALSE;
//		}
//		Predicate2Ar p = new Predicate2Ar(_term1, _term2, PredicateSymbol.EQ);
//		return p;
//	}
//
//	public Expression substitute(Expression _e, Expression _v) {
//		Expression term1 = getLeftExpr().substitute(_e, _v);
//		Expression term2 = getRightExpr().substitute(_e, _v);
//		setSubExpressions(new Expression[] { term1, term2 });
//		Expression simplify = simplify();
//		return simplify;
//	}
//
//	/**
//	 * Returns either this object either an object which is a simplification of
//	 * this one and which has an equivalent trutrh value of this object
//	 * Simplifications are done respecting these rules
//	 * <UL>
//	 * <li> if the predicate is the subtype predicate
//	 * <UL>
//	 * <li> if <code>term1 == JavaType._NULL</code> and term is a
//	 * <code>JavaRefernceType</code>
//	 * 
//	 * @return Predicate0ar.TRUE
//	 *         <li> else
//	 * @return <code>this</code>
//	 *         </UL>
//	 *         <li> if the predicate is the equal predicate then:
//	 *         <UL>
//	 *         <li> if the predicate is of the form <code>term1 == term2 </code>
//	 *         and term1.equals(term2) then
//	 * @return Predicate0ar.TRUE
//	 *         <li> if the predicate is of the form
//	 *         <code>Predicate0Ar.TRUE == Predicate0Ar.FALSE </code> or
//	 *         <code>Predicate0Ar.FALSE == Predicate0Ar.TRUE</code>
//	 * @return Predicate0Ar.FALSE
//	 *         <li> else
//	 * @return <code>this</code>
//	 *         </UL>
//	 * 
//	 * </UL>
//	 */
//	public Expression simplify() {
//		if (!SIMPLIFY_PRED) {
//			return this;
//		}
//		Expression term1 = getLeftExpr().simplify();
//		Expression term2 = getRightExpr().simplify();
//		if (getPredicateSymbol() == PredicateSymbol.SUBTYPE) {
//			if ((term1 == JavaType._NULL)
//					&& (term2 instanceof JavaReferenceType)) {
//				return Predicate0Ar.TRUE;
//			}
//			if ((term1 instanceof JavaReferenceType)
//					&& (term2 instanceof JavaReferenceType)) {
//				Predicate0Ar isSubType = (JavaReferenceType.subType(
//						(JavaReferenceType) term1, (JavaReferenceType) term2)) ? Predicate0Ar.TRUE
//						: Predicate0Ar.FALSE;
//				return isSubType;
//			}
//		}
//
//		if (getPredicateSymbol() == PredicateSymbol.EQ) {
//			if (term1 instanceof NumberLiteral
//					&& term2 instanceof NumberLiteral) {
//				Predicate p = simplifyNUMBERRELATION(term1, term2,
//						PredicateSymbol.EQ);
//				if (p != null) {
//					return p;
//				}
//			}
//			if (term1.equals(term2)) {
//				return Predicate0Ar.TRUE;
//			}
//			if ((term1 == Predicate0Ar.TRUE) && (term1 == Predicate0Ar.FALSE)) {
//				return Predicate0Ar.FALSE;
//			}
//			if ((term2 == Predicate0Ar.TRUE) && (term1 == Predicate0Ar.FALSE)) {
//				return Predicate0Ar.FALSE;
//			}
//		}
//		if ((getPredicateSymbol() == PredicateSymbol.LESS
//				|| getPredicateSymbol() == PredicateSymbol.LESSEQ
//				|| getPredicateSymbol() == PredicateSymbol.GRT 
//				|| getPredicateSymbol() == PredicateSymbol.GRTEQ)
//				&& term1 instanceof NumberLiteral
//				&& term2 instanceof NumberLiteral) {
//			Predicate p = simplifyNUMBERRELATION(term1, term2,
//					getPredicateSymbol());
//			if (p != null) {
//				return p;
//			}
//		}
//		setLeftExpr(term1);
//		setRightExpr(term2);
//		return this;
//	}
//
//	public Expression rename(Expression _expr1, Expression _expr2) {
//
//		Expression term1 = getLeftExpr().rename(_expr1, _expr2);
//		Expression term2 = getRightExpr().rename(_expr1, _expr2);
//		setSubExpressions(new Expression[] { term1, term2 });
//		return this;
//	}

	public String printCode1(BMLConfig conf) {
		String op = printRoot(conf);
		return getLeftExpr().printCode(conf) + op + getRightExpr().printCode(conf);

	}

//	public Expression copy() {
//
//		Expression term1Copy = getLeftExpr().copy();
//		Expression term2Copy = getRightExpr().copy();
//		Predicate2Ar copy = new Predicate2Ar(term1Copy, term2Copy,
//				getPredicateSymbol());
//		return copy;
//	}
//
//	/*
//	 * public Expression atState(int instrIndex) { Expression term1 =
//	 * getLeftExpr().atState(instrIndex); Expression term2 =
//	 * getRightExpr().atState(instrIndex); setSubExpressions(new
//	 * Expression[]{term1, term2}); return this; }
//	 */
//
//	/*	*//**
//			 * substitues all localvariable l by old(l) overriden method from
//			 * super class
//			 * 
//			 * @see bcexpression.Expression
//			 * @return
//			 */
//	/*
//	 * public Expression removeAtState(int index) { Expression term1 =
//	 * getLeftExpr().removeAtState(index); Expression term2 =
//	 * getRightExpr().removeAtState(index); setSubExpressions(new
//	 * Expression[]{term1, term2}); return this; }
//	 */
//	/*
//	 * public Expression localVarAtPreState() { Expression term1 =
//	 * getLeftExpr().localVarAtPreState(); Expression term2 =
//	 * getRightExpr().localVarAtPreState(); setSubExpressions(new
//	 * Expression[]{term1, term2}); return this; }
//	 */
//	public boolean equals(Formula formula) {
//		boolean eq = super.equals(formula);
//		// if the super class equals returns false then return false
//		if (!eq) {
//			return false;
//		}
//		if (getPredicateSymbol() != ((Predicate2Ar) formula)
//				.getPredicateSymbol()) {
//			return false;
//		}
//		return true;
//
//	}
}
