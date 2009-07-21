package annot.modifexpression;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;

public class SingleIndex extends SpecArray {

	public SingleIndex(Expression index ) {
		super(index);
	}
	
	public Expression getIndex() {
		return getSubExpressions()[0];
	}
	
	public String printCode1(BMLConfig conf) {
		String s = "" + getSubExpressions()[0].printCode(conf);   
		return s;
	}
}
