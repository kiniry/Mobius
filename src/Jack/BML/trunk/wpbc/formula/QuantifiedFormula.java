/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package formula;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class QuantifiedFormula extends  Formula {
	private Quantificator quantificator;
	private Formula subformula;
	
	public QuantifiedFormula(Formula _formula, Quantificator _q) {
		subformula = _formula;
		setQuantificator(_q);
	}
	/**
	 * @return Returns the quantificator.
	 */
	public Quantificator getQuantificator() {
		return quantificator;
	}
	/**
	 * @param quantificator The quantificator to set.
	 */
	private void setQuantificator(Quantificator quantificator) {
		this.quantificator = quantificator;
	}
	
	public Formula copy() {
		Formula  _subformula= subformula.copy();
		Formula _copy = new QuantifiedFormula(_subformula, quantificator);
		return _copy;
	}
}
