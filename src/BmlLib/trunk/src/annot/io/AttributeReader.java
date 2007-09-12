package annot.io;

import org.apache.bcel.classfile.Unknown;

import annot.attributes.ClassInvariant;
import annot.attributes.MethodSpecification;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.JavaType;
import annot.bcexpression.NumberLiteral;
import annot.constants.BCConstant;
import annot.constants.BCConstantUtf8;
import annot.formula.Formula;
import annot.formula.Predicate0Ar;
import annot.formula.Predicate2Ar;
import annot.formula.QuantifiedFormula;
import annot.textio.IDisplayStyle;

public class AttributeReader {

	private BCClass bcc;
	private BCMethod method;
	private byte[] input;
	private int pos;
	private int length;
	private String attrName = "?"; // debug
	public BoundVar[] env;  //vector

	public AttributeReader(BCClass bcc) {
		this.bcc = bcc;
	}

	public AttributeReader(BCMethod bcm) {
		this.bcc = bcm.bcc;
		this.method = bcm;
	}

	public void readAttribute(Unknown ua) throws ReadAttributeException {
		String aname = attrName = ua.getName();
		input = ua.getBytes();
		length = ua.getLength();
		pos = 0;
		if (aname.equals(IDisplayStyle.__mspec)) {
			MLog.putMsg(MLog.PInfo, "    reading attribute: "
					+ IDisplayStyle.__mspec);
			method.mspec = new MethodSpecification(method, this);
		} else if (aname.equals(IDisplayStyle.__classInvariant)) {
			MLog.putMsg(MLog.PInfo, "    reading attribute: "
					+ IDisplayStyle.__classInvariant);
			bcc.invariant = new ClassInvariant(bcc, this);
		} else if (aname.equals(IDisplayStyle.__assertTable)) {
			MLog.putMsg(MLog.PInfo, "    reading attribute: "
					+ IDisplayStyle.__assertTable);
			method.amap.atab.load(this);
		} else if (aname.equals(IDisplayStyle.__second_cp)) {
			MLog.putMsg(MLog.PInfo, "    reading attribute: "
					+ IDisplayStyle.__second_cp);
			bcc.cp.scp.load(this);
		} else {
			MLog.putMsg(MLog.PTodo, "    unrecognized attribute: " + aname);
		}
		if (pos != length)
			throw new ReadAttributeException((length - pos) + " of " + length
					+ " bytes unread!");
	}

	private void chkRange(int n) throws ReadAttributeException {
		if (pos + n > length)
			throw new ReadAttributeException("end of input stream in "
					+ attrName + " (size=" + length + ")");
	}

	public int readByte() throws ReadAttributeException {
		chkRange(1);
		int b = (input[pos] & 0xff);
		pos++;
		return b;
	}

	public int readShort() throws ReadAttributeException {
		chkRange(2);
		int s = ((input[pos] & 0xff) << 8) + (input[pos + 1] & 0xff);
		pos += 2;
		return s;
	}

	public int readInt() throws ReadAttributeException {
		chkRange(4);
		int i = (input[pos] & 0xff) << 24;
		i += (input[pos + 1] & 0xff) << 16;
		i += (input[pos + 2] & 0xff) << 8;
		i += input[pos + 3] & 0xff;
		pos += 4;
		return i;
	}

	public String readUtf8() throws ReadAttributeException {
		// XXX check annotated .class file format compatibility
		int l = readByte();
		String ret = "";
		for (int i = 0; i < l; i++)
			ret += (char) readByte();
		return ret;
	}

	public int readAttributesCount() throws ReadAttributeException {
		return readShort();
	}

	public String findString(int index) throws ReadAttributeException {
		BCConstant c = bcc.cp.getAt(index);
		if (c instanceof BCConstantUtf8)
			return ((BCConstantUtf8) c).data;
		throw new ReadAttributeException("invalid constant index: " + index);
	}

	public BCExpression readExpression() throws ReadAttributeException {
		int b = readByte();
		switch (b) {
		case Code.TRUE:
			return Predicate0Ar.TRUE;
		case Code.FALSE:
			return Predicate0Ar.FALSE;
		case Code.AND:
		case Code.OR:
		case Code.IMPLIES:
		case Code.NOT:
			// FIXME! not supported by .class file format!
		case Code.EQUIV:
		case Code.NOTEQUIV:
			return new Formula(this, b);
		case Code.LESS:
		case Code.LESSEQ:
		case Code.EQ:
		case Code.NOTEQ:
		case Code.GRT:
		case Code.GRTEQ:
			return new Predicate2Ar(this, b);
		case Code.INT_LITERAL:
			return new NumberLiteral(this, b);
		case Code.FORALL:
		case Code.EXISTS:
		case Code.FORALL_WITH_NAME:
		case Code.EXISTS_WITH_NAME:
			return new QuantifiedFormula(this, b);
		case Code.BOUND_VAR:
			return BoundVar.getBoundVar(this);
		case Code.JAVA_TYPE:
			int i = readShort();
			BCConstant c = bcc.cp.getAt(i);
			if (!(c instanceof BCConstantUtf8))
				throw new ReadAttributeException(
						"Utf8 expected as javaType name");
			String name = ((BCConstantUtf8) c).data;
			return JavaType.getJavaType(name);
		default:
			throw new ReadAttributeException("Unknown expression code: " + b);
		}
	}

}
