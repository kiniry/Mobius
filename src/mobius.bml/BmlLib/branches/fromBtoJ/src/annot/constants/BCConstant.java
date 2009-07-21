package annot.constants;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;

public class BCConstant extends Expression {
	private int cpIndex;
//	private byte tag;
//	//used just for the arraylength constant
	public BCConstant() {
	}
	public BCConstant(int _cpIndex) {
		cpIndex = _cpIndex;
	}
	public int getCPIndex() {
		return cpIndex;
	}

	public String printCode1(BMLConfig conf) {
		System.out.println("Unknown constant #"+cpIndex);
		return "#" + cpIndex;
	}
	
	public String toString() {
		return "#" + cpIndex;
	}
	
//	public byte getTag() {
//		return tag;
//	}
//	
//	public boolean equals(BCConstant _constant) {
//		if (_constant == this) {
//			return true;
//		}
//		if ((this instanceof ArrayLengthConstant)
//				&& (_constant instanceof ArrayLengthConstant)) {
//			return true;
//		}
//		return false;
//	}
//	
//	public Expression substitute(Expression _e1, Expression _e2) {
//		if (this == _e1 ) {
//			return _e2;
//		}
//		return this;
//	}
//
	public Expression copy() {
		// TODO Auto-generated method stub
		return this;
	}
}
