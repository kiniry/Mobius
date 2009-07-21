package annot.formula;

import annot.bcexpression.Expression;

public class Predicate extends Formula {
	private byte predicateSymbol;
	
	public Predicate(){
	}
//	public Predicate(
//			Expression _term,
//			byte _predicateSymbol
//			){
//		super(_term);
//		predicateSymbol = _predicateSymbol;
//	}
	public Predicate(
			Expression _term1,
			Expression _term2,
			byte _predicateSymbol
			){
		super(_term1, _term2);
		predicateSymbol = _predicateSymbol;
	}
//	
//	protected void setPredicateSymbol(byte _predicateSymbol) {
//		predicateSymbol =  _predicateSymbol;
//	}

	public byte getPredicateSymbol() {
		return predicateSymbol;
	}
}
