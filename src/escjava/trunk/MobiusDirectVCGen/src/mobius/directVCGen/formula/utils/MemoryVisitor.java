package mobius.directVCGen.formula.utils;

import java.util.Stack;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.FormulaVisitor;
import mobius.directVCGen.formula.IFormula;


public class MemoryVisitor extends FormulaVisitor {	
	private Stack<Integer> slots = new Stack<Integer>();
	private Stack<IFormula> fathers = new Stack<IFormula>();
	public void visitChildren (IFormula f) throws FormulaException {
		fathers.push(f);
		int i = 0;
		for (IFormula child: f) {
			slots.push(i);
			child.accept(this);
			slots.pop();
			i++;
		}
		fathers.pop();
	}
	
	public IFormula getFather() {
		return fathers.peek();
	}
	public int getSlot() {
		return slots.peek();
	}
	
	public void replaceWith(IFormula replacement) {
		getFather().set(getSlot(), replacement);
	}
}
