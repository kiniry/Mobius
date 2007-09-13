package annot.bcexpression;

import annot.formula.QuantifiedFormula;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

public class BoundVar extends BCExpression {

	public static final boolean goWriteVarNames = true;

	private JavaType type;
	private int index;
	private QuantifiedFormula qf;
	private String vname;

	public BoundVar(JavaType jt, int index, QuantifiedFormula qf, String vname) {
		super(Code.BOUND_VAR);
		this.type = jt;
		this.index = index;
		this.qf = qf;
		setVname(vname);
	}

	public static BoundVar getBoundVar(AttributeReader ar)
			throws ReadAttributeException {
		int i = ar.readShort();
		return ar.bvars.elementAt(i);
	}

	@Override
	public int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public String printCode1(BMLConfig conf) {
		String n = getVname();
		if (n != null)
			return "" + n;
		return "var[" + index + "]";
	}

	@Override
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new RuntimeException(
				"read() method unavaliable, use getBoundVar() instead");
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.BOUND_VAR);
		aw.writeShort(index);
	}

	@Override
	public JavaType getType1() {
		return type;
	}

	@Override
	public void init() {
	}

	@Override
	public String toString() {
		return "var[" + index + "]";
	}

	public String getVname() {
		return vname;
	}

	public void setVname(String vname) {
		this.vname = vname;
	}

}
