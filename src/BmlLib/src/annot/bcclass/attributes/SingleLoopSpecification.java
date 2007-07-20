package annot.bcclass.attributes;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;
import annot.bcexpression.NumberLiteral;
import annot.formula.Formula;

public class SingleLoopSpecification {
	// the intrsuction index in the bytecode array that corresponds to the beginning of the loop
	private int pcIndex;
	private Formula invariant;
	private ModifiesSet modifies;
	private Expression decreases;
	
	public SingleLoopSpecification(int _cpIndex, ModifiesSet _modifies, Formula _invariant, Expression _decreases) {
		pcIndex  = _cpIndex;
		invariant = _invariant;
		decreases = _decreases;
		modifies = _modifies;
	}

	public String printCode(BMLConfig conf) {
		String code = "("+pcIndex+")";
		code += conf.newLine() + "loop_invariant " + invariant.printLine(conf, 17);
		code += conf.newLine() + "loop_modifies " + modifies.printCode(conf, 14);
		String dec = decreases.printLine(conf, 12);
		if (!"1".equals(dec)) // TODO zr�b cos z tym
			code += conf.newLine() + "decreases " + dec;
		return conf.addComment(code);
	}
	
	/**
	 * @return
	 */
	public Expression getDecreases() {
		return decreases.copy();
	}

	/**
	 * @return
	 */
	public Formula getInvariant() {
		return (Formula)invariant.copy();
	}

	/**
	 * @return
	 */
	public ModifiesSet getModifies() {
		return modifies;
	}



	/**
	 * @param formula
	 */
	public void setInvariant(Formula formula) {
		invariant = formula;
	}

	/**
	 * @return the index in the bytecode at which the loop that is 
	 *  specified with this invariant starts 
	 */
	public int getLoopIndex() {
		return pcIndex;
	}
}
