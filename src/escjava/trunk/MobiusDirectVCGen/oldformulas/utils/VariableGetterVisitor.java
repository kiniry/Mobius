package mobius.directVCGen.formula.utils;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.FormulaVisitor;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.Variable;


public class VariableGetterVisitor extends FormulaVisitor {
	private final Vector<Variable> vars = new Vector<Variable>();
	
	protected VariableGetterVisitor () {
		
	}
	
	private Vector<Variable> getCollectedVars() {
		return vars;
	}
	
	public static Vector<Variable> collectVars(IFormula f) {
		VariableGetterVisitor vgv = new VariableGetterVisitor();
		try {
			f.accept(vgv);
		} catch (FormulaException e) {
			e.printStackTrace();
		}
		return vgv.getCollectedVars();
	}
	
	public void visitVariable(Variable v) throws FormulaException {
		vars.add(v);
	}
}
