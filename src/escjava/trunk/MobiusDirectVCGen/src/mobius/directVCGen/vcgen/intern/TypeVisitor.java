package mobius.directVCGen.vcgen.intern;

import mobius.directVCGen.formula.Formula;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter;
import escjava.sortedProver.NodeBuilder.Sort;
import javafe.ast.PrimitiveType;
import javafe.ast.Type;

public class TypeVisitor extends ABasicVisitor {
	protected static TypeVisitor inst = new TypeVisitor();
	public static Sort convert2Type(Type type) {
		;
		Sort t = (Sort)type.accept(inst, Formula.getCurrentLifter().sortAny);
		
		return t;
	}
	
	public Object visitPrimitiveType(PrimitiveType pt, Object o) {
		//System.out.println(TagConstants.toString(pt.tag));
		Lifter lf = Formula.getCurrentLifter();
		switch (pt.tag) {
			case TagConstants.INTTYPE:
			case TagConstants.LONGTYPE:
			case TagConstants.BYTETYPE:
			case TagConstants.SHORTTYPE:
			case TagConstants.CHARTYPE:
				return lf.sortInt;
			case TagConstants.BOOLEANTYPE:
				return lf.sortBool;
			case TagConstants.VOIDTYPE:
				return lf.sortPred; // void type is more or less prop type
				// in my world ;)
				
			case TagConstants.DOUBLETYPE:
			case TagConstants.FLOATTYPE:
				return lf.sortReal;
			case TagConstants.NULLTYPE:
				return lf.sortRef;
			case TagConstants.ERRORTYPE:
			throw new IllegalArgumentException("Unmanaged construct :" +
						TagConstants.toString(pt.tag) +" " +  pt);
			default:
				throw new IllegalArgumentException("Unknown construct :" +
						TagConstants.toString(pt.tag) +" " +  pt);

		}
	}
	
	
}
