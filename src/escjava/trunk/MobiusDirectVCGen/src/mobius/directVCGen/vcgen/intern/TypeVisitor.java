package mobius.directVCGen.vcgen.intern;

import javafe.ast.PrimitiveType;
import javafe.ast.Type;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import escjava.ast.TagConstants;
import escjava.sortedProver.NodeBuilder.Sort;

public class TypeVisitor extends ABasicVisitor {
	protected static TypeVisitor inst = new TypeVisitor();
	public static Sort convert2Type(Type type) {
		Sort t = (Sort)type.accept(inst, Formula.sort);
		
		return t;
	}
	
	public Object visitPrimitiveType(PrimitiveType pt, Object o) {
		//System.out.println(TagConstants.toString(pt.tag));
		switch (pt.tag) {
			case TagConstants.INTTYPE:
			case TagConstants.LONGTYPE:
			case TagConstants.BYTETYPE:
			case TagConstants.SHORTTYPE:
			case TagConstants.CHARTYPE:
				return Num.sortInt;
			case TagConstants.BOOLEANTYPE:
				return Bool.sort;
			case TagConstants.VOIDTYPE:
				return Logic.sort; // void type is more or less prop type
				// in my world ;)
				
			case TagConstants.DOUBLETYPE:
			case TagConstants.FLOATTYPE:
				return Num.sortReal;
			case TagConstants.NULLTYPE:
				return Ref.sort;
			case TagConstants.ERRORTYPE:
			throw new IllegalArgumentException("Unmanaged construct :" +
						TagConstants.toString(pt.tag) +" " +  pt);
			default:
				throw new IllegalArgumentException("Unknown construct :" +
						TagConstants.toString(pt.tag) +" " +  pt);

		}
	}
	
	
}
