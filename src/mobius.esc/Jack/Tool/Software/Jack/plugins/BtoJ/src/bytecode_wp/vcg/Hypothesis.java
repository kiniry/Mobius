package bytecode_wp.vcg;


import bytecode_wp.bcexpression.Expression;
import bytecode_wp.formula.Formula;

public class Hypothesis {
	private Formula hyp;
	
	
	
	
	/**
	 * the index of the instruction from which this hypothesis comes from
	 */
	private int fromInstr;

	
	
	public Hypothesis (int instrId ,Formula  f) {
		hyp = f;
		fromInstr = instrId;
	}
	
	
	public Formula getFormula() {
		return hyp;
	}
	
	public int getPos() {
		return fromInstr;
		
	}
	
	public String toString() {
		return  fromInstr + ":" + hyp.toString();
	}


	public void substitute(Expression e1, Expression e2) {
		hyp = (Formula) hyp.substitute(e1, e2);
	}
	
	public void simplify() {
		hyp = (Formula) hyp.simplify();
	}
	
	
	public Hypothesis copy() {
		Formula fCopy = (Formula)hyp.copy();
		Hypothesis hCopy = new Hypothesis(fromInstr, fCopy);
		return hCopy;
	}
	
	public void atState(int pos, Expression expr) {
		hyp = (Formula) hyp.atState(pos, expr );
	}
	
	public boolean equals(Hypothesis h) {
		if (h == null) {
			return false;
		}
		Formula f = h.getFormula();
		if (f.equals(hyp)) {
			return true;
		}
		return false;
	}




	public void loopModifArrayAtState(int instrIndex, Expression expr) {
		hyp = (Formula) hyp.loopModifArrayAtState(instrIndex, expr );	
	}
}
