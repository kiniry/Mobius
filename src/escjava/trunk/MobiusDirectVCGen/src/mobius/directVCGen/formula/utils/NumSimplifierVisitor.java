package mobius.directVCGen.formula.utils;


import java.util.Vector;

import mobius.directVCGen.formula.DummyFormula;
import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.num.INumVisitor;
import mobius.directVCGen.formula.expression.num.NAdd;
import mobius.directVCGen.formula.expression.num.NInt;
import mobius.directVCGen.formula.expression.num.NLong;
import mobius.directVCGen.formula.expression.num.NMinus;
import mobius.directVCGen.formula.expression.num.ANumValue;


public class NumSimplifierVisitor extends MemoryVisitor implements INumVisitor{
	protected NumSimplifierVisitor() {
		
	}
	public int collectValues(IFormula f, Vector<Long> l) throws FormulaException {
		visitChildren(f);
		int id = 0;
		for(IFormula child: f) {
			if(!isNumValue(child))
				return 0;
			if(child.getID() > id) {
				id = child.getID();
			}
			l.add(((ANumValue) child).getNormalValue());
		}
		return id;
	}
	
	public void visitNAdd(NAdd na) throws FormulaException {
		Vector<Long> vec = new Vector<Long>();
		int id = collectValues(na, vec);
		if(id == 0)
			return;
		long num1 = vec.get(0);
		long num2 = vec.get(1);
		switch(id) {
			case IFormula.nByte:
				byte b1 = (byte) num1;
				byte b2 = (byte) num2;
				replaceWith(new NInt(b1 + b2));
				break;
			case IFormula.nShort:
				short s1 = (short) num1;
				short s2 = (short) num2;
				replaceWith(new NInt(s1 + s2));
				break;
			case IFormula.nInt:
				int v1 = (int) num1;
				int v2 = (int) num2;
				replaceWith(new NInt(v1 + v2));
				break;
			case IFormula.nLong:
				long l1 = (long) num1;
				long l2 = (long) num2;
				replaceWith(new NLong(l1 + l2));
				break;
			
			default:
				return;
		}
	}
	public void visitNMinus(NMinus nm) throws FormulaException {
		visitChildren(nm);
		
		IFormula f= nm.get(0);
		if(!isNumValue(f))
			return;
		int id = f.getID();
		long num1 = ((ANumValue) f).getNormalValue();
		
		switch(id) {
			case IFormula.nShort:
				byte b1 = (byte) num1;
				replaceWith(new NInt(- b1));
				break;
			case IFormula.nByte:
				short s1 = (short) num1;
				replaceWith(new NInt(- s1));
			case IFormula.nInt:
				int v1 = (int) num1;
				replaceWith(new NInt(- v1));
				break;
			case IFormula.nLong:
				long l1 = (long) num1;
				replaceWith(new NLong(- l1));
				break;
				
		}
	}
	
	public static boolean isNumValue(IFormula f) {
		int id = f.getID();
		switch (id) {
			case IFormula.nInt:
			case IFormula.nLong:
			case IFormula.nShort:
			case IFormula.nByte:
				return true;
			default:
				return false;
		}
	}

	public static IFormula simplifyFormula (IFormula f) {
		Vector<IFormula> v = new Vector<IFormula>();
		v.add(f);
		DummyFormula dummy = new DummyFormula(v);
		try {
			dummy.accept(new NumSimplifierVisitor());
		} catch (FormulaException e) {
			e.printStackTrace();
		}
		return dummy.get(0);
	}



}
