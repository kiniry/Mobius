package mobius.directVCGen.vcgen.expression;

import javafe.ast.ArrayType;
import javafe.ast.ClassLiteral;
import javafe.ast.ErrorType;
import javafe.ast.JavafePrimitiveType;
import javafe.ast.PrimitiveType;
import javafe.ast.Type;
import javafe.ast.TypeName;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.vcgen.ABasicVisitor;
import escjava.ast.TagConstants;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * @deprecated should be useless
 * @author J. Charles
 */
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
	  public /*@non_null*/ Object visitType(/*@non_null*/ Type x, Object o) {
		    return visitASTNode(x, o);
		  }

		  public /*@non_null*/ Object visitErrorType(/*@non_null*/ ErrorType x, Object o) {
		    return visitType(x, o);
		  }


		  public /*@non_null*/ Object visitJavafePrimitiveType(/*@non_null*/ JavafePrimitiveType x, Object o) {
		    return visitPrimitiveType(x, o);
		  }

		  public /*@non_null*/ Object visitTypeName(/*@non_null*/ TypeName x, Object o) {
		    return visitType(x, o);
		  }

		  public /*@non_null*/ Object visitArrayType(/*@non_null*/ ArrayType x, Object o) {
		    return visitType(x, o);
		  }

		  public /*@non_null*/ Object visitClassLiteral(/*@non_null*/ ClassLiteral x, Object o) {
		    return visitExpr(x, o);
		  }
		  
}
