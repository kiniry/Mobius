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
public class QuantifiedFormula extends Formula {
	private Quantificator[] quantificators;
	private Formula subformula;

	public QuantifiedFormula(Formula _formula, Quantificator _q) {
		subformula = _formula;
		quantificators = new Quantificator[1];
		quantificators[0] = _q;
	}

	public QuantifiedFormula(Formula _formula, Quantificator[] _q) {
		subformula = _formula;
		quantificators = _q;
	}

	/**
	 * @return Returns the quantificator.
	 */
	public Quantificator getQuantificator() {
		return quantificators[0];
	}

	/**
	 * @return Returns the quantificator.
	 */
	public Quantificator getQuantificator(int i) {
		return quantificators[i];
	}

	public Formula copy() {
		Formula _subformula = subformula.copy();
		Quantificator[] q = new Quantificator[quantificators.length];
		for (int i = 0; i < quantificators.length; i++) {
			q[i] = quantificators[i].copy();
		}
		Formula _copy = new QuantifiedFormula(_subformula, q);
		return _copy;
	}
	
	public String toString() { 
		String s = toString();
		for (int i =0 ; i < quantificators.length; i++ ) {
			s = s  + quantificators[i];
		}
		s = s + subformula;
		return s;
	}
}
