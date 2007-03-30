package mobius.directVCGen.vcgen.intern;

import escjava.ast.TagConstants;
import javafe.ast.PrimitiveType;
import mobius.directVCGen.formula.type.Type;

public class TypeVisitor extends ABasicVisitor {
	protected static TypeVisitor inst = new TypeVisitor();
	public static Type convert2Type(javafe.ast.Type type) {
		Type t = (Type)type.accept(inst, Type.undef);
		
		return t;
	}
	
	public Object visitPrimitiveType(PrimitiveType pt, Object o) {
		//System.out.println(TagConstants.toString(pt.tag));
		switch (pt.tag) {
			case TagConstants.INTTYPE:
				return Type.numInt;
			case TagConstants.BYTETYPE:
				return Type.numByte;
			case TagConstants.SHORTTYPE:
				return Type.numShort;
			case TagConstants.LONGTYPE:
				return Type.numLong;
			case TagConstants.BOOLEANTYPE:
				return Type.bool;
			case TagConstants.VOIDTYPE:
				return Type.prop; // void type is more or less prop type
				// in my world ;)
				
			case TagConstants.DOUBLETYPE:
			case TagConstants.ERRORTYPE:
			case TagConstants.CHARTYPE:
			case TagConstants.NULLTYPE:
			case TagConstants.FLOATTYPE:
			throw new IllegalArgumentException("Unmanaged construct :" +
						TagConstants.toString(pt.tag) +" " +  pt);
			default:
				throw new IllegalArgumentException("Unknown construct :" +
						TagConstants.toString(pt.tag) +" " +  pt);

		}
	}
	
	
}
