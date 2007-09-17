package annot.formula;

import java.util.Iterator;
import java.util.Vector;

import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;
import annot.textio.Priorities;

public class QuantifiedFormula extends AbstractFormula {

	private Vector<BoundVar> vars;

	public QuantifiedFormula(int connector) {
		super(connector);
	}

	public QuantifiedFormula(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	private String printRoot() {
		switch (getConnector()) {
		case Code.FORALL:
		case Code.FORALL_WITH_NAME:
			return "forall";
		case Code.EXISTS:
		case Code.EXISTS_WITH_NAME:
			return "exists";
		default:
			return "?";
		}
	}

	@Override
	public String printCode1(BMLConfig conf) {
		String code = printRoot();
		code += IDisplayStyle.expr_block_start;
		Iterator<BoundVar> iter = vars.iterator();
		while (iter.hasNext()) {
			BoundVar bv = iter.next();
			code += " " + bv.getType().printCode1(conf);// !
			code += " " + bv.printCode1(conf);// !
		}
		code += "; ";
		code += IDisplayStyle.expr_block_end;
		String str = getSubExpr(0).printCode(conf);
		if (IDisplayStyle.go3argQuantifiers)
			str = str.substring(1, str.length() - 1);
		code += str;
		return code;
	}

	@Override
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		int n = ar.readByte();
		int bvc = ar.getBvarCount();
		for (int i = 0; i < n; i++) {
			BCExpression expr = ar.readExpression();
			if (!(expr instanceof JavaType))
				throw new ReadAttributeException("JavaType expected, read "
						+ expr.getClass().toString());
			JavaType jt = (JavaType) expr;
			BoundVar bv = new BoundVar(jt, bvc + i, this, null);
			if ((root == Code.FORALL_WITH_NAME)
					|| (root == Code.EXISTS_WITH_NAME)) {
				int cpIndex = ar.readShort();
				if (cpIndex != 0) {// ?
					String vname = ar.findString(cpIndex);
					bv.setVname(vname);
				}
			}
			ar.getBvars().add(bv);
			vars.add(bv);
		}
		setSubExpr(0, ar.readExpression());
		for (int i = 0; i < n; i++)
			ar.getBvars().remove(ar.getBvarCount() - 1);
	}

	private int chkConnector() {
		if (BoundVar.goWriteVarNames) {
			if (getConnector() == Code.FORALL)
				return Code.FORALL_WITH_NAME;
			if (getConnector() == Code.EXISTS)
				return Code.EXISTS_WITH_NAME;
		} else {
			if (getConnector() == Code.FORALL_WITH_NAME)
				return Code.FORALL;
			if (getConnector() == Code.EXISTS_WITH_NAME)
				return Code.EXISTS;
		}
		return getConnector();
	}

	@Override
	public void write(AttributeWriter aw) {
		int conn = chkConnector();
		aw.writeByte(conn);
		aw.writeByte(vars.size());
		Iterator<BoundVar> iter = vars.iterator();
		while (iter.hasNext()) {
			BoundVar bv = iter.next();
			bv.getType().write(aw);
			if (BoundVar.goWriteVarNames) {
				String vname = bv.getVname();
				if (vname == null) {
					aw.writeShort(0);
				} else {
					int index = aw.findConstant(vname);
					aw.writeShort(index);
				}
			}
		}
		writeSubExpressions(aw);
	}

	@Override
	public void init() {
		setSubExprCount(1);
		this.vars = new Vector<BoundVar>();
	}

	@Override
	public String toString() {
		String code = printRoot();
		Iterator<BoundVar> iter = vars.iterator();
		while (iter.hasNext())
			code += " " + iter.next().toString();
		code += " " + getSubExpr(0).toString();
		return code;
	}

	@Override
	public int getPriority() {
		return Priorities.getPriority(getConnector());
	}

	@Override
	public JavaType getType1() {
		if (getSubExpr(0).getType() != JavaType.JavaBool)
			return null;
		return JavaType.JavaBool;
	}

	public void addVariable(BoundVar bv) {
		if (getSubExpr(0) != null)
			throw new RuntimeException("formula is already set!");
		vars.add(bv);
	}

	public void setFormula(BCExpression expression) {
		if (getSubExpr(0) != null)
			throw new RuntimeException("formula is already set!");
		setSubExpr(0, expression);
	}

	public BoundVar getVar(int index) {
		return vars.elementAt(index);
	}

	public int getLength() {
		return vars.size();
	}

}
