package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.bcexpression.JavaBasicType;
import annot.bcexpression.JavaType1;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

public class ModifyList extends BCExpression {

	public ModifyList() {
		super(Code.MODIFIES_LIST);
		setSubExprCount(0);
	}

	public ModifyList(ModifyExpression[] subExpr) {
		super(Code.MODIFIES_LIST);
		setSubExprCount(subExpr.length);
		for (int i=0; i<subExpr.length; i++)
			setSubExpr(i, subExpr[i]);
	}

	public ModifyList(AttributeReader ar)
			throws ReadAttributeException {
		super(ar, -1);
	}

	@Override
	protected JavaType1 checkType1() {
		return JavaBasicType.ModifyExpressionType;
	}

	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public JavaType1 getType() {
		return JavaBasicType.ModifyExpressionType;
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		if (getSubExprCount() == 0)
			return "everything";
		String code = "";
		for (int i=0; i<getSubExprCount(); i++) {
			if (i > 0)
				code += ", ";
			String line = getSubExpr(i).printCode(conf);
			code += line.substring(0, line.length() - 2).substring(2);
		}
		return code;
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		int size = ar.readAttributesCount();
		setSubExprCount(size);
		for (int i=0; i<size; i++) {
			ModifyExpression me = ar.readModifyExpression();
			setSubExpr(i, me);
		}
	}

	@Override
	public String toString() {
		if (getSubExprCount() == 0)
			return "<<empty list>>";
		String code = "";
		for (int i=0; i<getSubExprCount(); i++) {
			if (i > 0)
				code += ", ";
			code += getSubExpr(i).toString();
		}
		return code;
	}

	@Override
	public void write(AttributeWriter aw) {
		if (getSubExprCount() == 0)
			addModify(ModifyExpression.Everything);
		aw.writeAttributeCount(getSubExprCount());
		writeSubExpressions(aw);
	}

	public void addModify(ModifyExpression expr) {
		//XXX slow
		BCExpression[] sub = getAllSubExpr();
		setSubExprCount(sub.length + 1);
		for (int i=0; i<sub.length; i++)
			setSubExpr(i, sub[i]);
		setSubExpr(sub.length , expr);
	}

	public boolean isEmpty() {
		if (getSubExprCount() == 0)
			return true;
		return (getSubExprCount() == 1)
			&& (getSubExpr(0) == ModifyExpression.Everything);
	}
}
