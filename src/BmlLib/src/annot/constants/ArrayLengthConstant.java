package annot.constants;

public class ArrayLengthConstant  extends BCConstantFieldRef {
	public static final ArrayLengthConstant ARRAYLENGTHCONSTANT = new ArrayLengthConstant();
		
	private ArrayLengthConstant() {
	}
	
	public String toString() {
		return "_length" ;
	}
	
//	public boolean equals(Expression expr ) {
//		if (expr == ARRAYLENGTHCONSTANT) {
//			return true;
//		}
//		return false;
//	}
//	
//	public BCConstantClass getConstantClass() {
//		return null;
//	}
//	
//	public boolean isStatic() {
//		return false;
//	}
//    public Expression getType() {
//        return JavaType.JavaINT;
//    }
}
