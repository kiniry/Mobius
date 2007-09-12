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
import annot.textio.Priorities;

public class QuantifiedFormula extends AbstractFormula {

	private boolean forall;
	private Vector<BoundVar> vars;

	public QuantifiedFormula(boolean forall) {
		super(forall ? Code.FORALL : Code.EXISTS);
		this.forall = forall;
	}

	public QuantifiedFormula(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	public int getPriority() {
		return Priorities.getPriority(connector);
	}

	@Override
	public String printCode1(BMLConfig conf) {
		String code = forall ? "forall" : "exists";
		Iterator<BoundVar> iter = vars.iterator();
		while (iter.hasNext())
			code += " " + iter.next().printCode(conf);
		code += " " + subExpr[0].printCode(conf);
		return code;
	}

	@Override
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		forall = (root == Code.FORALL) || (root == Code.FORALL_WITH_NAME);
		int n = ar.readByte();
		ar.env = new BoundVar[n];
		// XXX nested quantifiers unsupported!
		for (int i = 0; i < n; i++) {
			BCExpression expr = ar.readExpression();
			if (!(expr instanceof JavaType))
				throw new ReadAttributeException("JavaType expected, read "
						+ expr.getClass().toString());
			JavaType jt = (JavaType) expr;
			BoundVar bv = new BoundVar(jt, i, this, null);
			if ((root == Code.FORALL_WITH_NAME)
					|| (root == Code.EXISTS_WITH_NAME)) {
				int cpIndex = ar.readShort();
				if (cpIndex != 0) {// ?
					String vname = ar.findString(cpIndex);
					bv.setVname(vname);
				}
			}
			ar.env[i] = bv;
			vars.add(bv);
		}
		subExpr[0] = ar.readExpression();
	}

	@Override
	public void write(AttributeWriter aw) {
		int conn = connector;
		if (BoundVar.goWriteVarNames) {
			if (conn == Code.FORALL)
				conn = Code.FORALL_WITH_NAME;
			if (conn == Code.EXISTS)
				conn = Code.EXISTS_WITH_NAME;
		} else {
			if (conn == Code.FORALL_WITH_NAME)
				conn = Code.FORALL;
			if (conn == Code.EXISTS_WITH_NAME)
				conn = Code.EXISTS;
		}
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

	public void addVariable(BoundVar bv) {
		if (subExpr[0] != null)
			throw new RuntimeException("formula is already set!");
		vars.add(bv);
	}

	public void setFormula(AbstractFormula af) {
		if (subExpr[0] != null)
			throw new RuntimeException("formula is already set!");
		subExpr[0] = af;
	}

	public BoundVar getVar(int index) {
		return vars.elementAt(index);
	}

	public int getLength() {
		return vars.size();
	}

	@Override
	public void init() {
		this.subExpr = new BCExpression[1];
		vars = new Vector<BoundVar>();
	}

	@Override
	public String toString() {
		String code = forall ? "forall" : "exists";
		Iterator<BoundVar> iter = vars.iterator();
		while (iter.hasNext())
			code += " " + iter.next().toString();
		code += " " + subExpr[0].toString();
		return code;
	}

}
