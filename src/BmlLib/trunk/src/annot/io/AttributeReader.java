package annot.io;

import java.util.Vector;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.Unknown;

import annot.attributes.ClassInvariant;
import annot.attributes.MethodSpecification;
import annot.bcclass.BCClass;
import annot.bcclass.BCConstantPool;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.bcexpression.ArithmeticExpression;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BCFieldRef;
import annot.bcexpression.BCLocalVariable;
import annot.bcexpression.BoundVar;
import annot.bcexpression.ConditionalExpression;
import annot.bcexpression.FieldAccess;
import annot.bcexpression.JavaType1;
import annot.bcexpression.NULL_CLASS;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.OLD;
import annot.bcexpression.UnaryArithmeticExpression;
import annot.formula.AbstractFormula;
import annot.formula.Formula;
import annot.formula.Predicate0Ar;
import annot.formula.Predicate2Ar;
import annot.formula.QuantifiedFormula;
import annot.textio.IDisplayStyle;

/**
 * This class is responsible for loading BML attributes from
 * BCEL's Unknown atribute. It should be created for a BCClass
 * or BCMethod, BML attribute can be loaded using
 * {@link #readAttribute(Unknown)} method.
 * This class contains data 'stream' (as a byte array) and
 * environment needed to read an expression (eg. bound
 * variables table).
 * 
 * @author tomekb
 */
public class AttributeReader {

	/**
	 * Class containing currently read attributes.
	 */
	private BCClass bcc;

	/**
	 * Method containing currently read attribute, if any.
	 */
	private BCMethod method;

	/**
	 * Input stream (from BCEL's Unknown attribute).
	 */
	private byte[] input;

	/**
	 * Current position in input stream.
	 */
	private int pos;

	/**
	 * Initial length of input stream (after finished reading
	 * of attribute, <code>pos</code> should be equal to
	 * <code>length</code>.
	 */
	private int length;

	/**
	 * Current attribute's name, used for displaying error
	 * message only.
	 */
	private String attrName = "?"; // debug

	// environment:
	
	/**
	 * Bound variables table. Contains declared (currently
	 * visible) bound variables, with right-most, most
	 * recently declared at the end.
	 */
	private Vector<BoundVar> bvars;

	/**
	 * A Constructor used for reading class attributes.
	 * 
	 * @param bcc - class that read attributes should be
	 * attached to.
	 */
	public AttributeReader(BCClass bcc) {
		this.bcc = bcc;
		this.bvars = new Vector<BoundVar>();
	}

	/**
	 * A Constructor used for reading method attributes.
	 * 
	 * @param bcm - method that read attributes should be
	 * attached to.
	 */
	public AttributeReader(BCMethod bcm) {
		this.bcc = bcm.getBcc();
		this.method = bcm;
		this.bvars = new Vector<BoundVar>();
	}

	/**
	 * Creates proper BML attribute (IBCAttribute, not exactly
	 * BCPrintableAttribute) depending on given Unknown
	 * attribute's name, loads it from given Unknown attribute
	 * and attach to BCClass or BCMethod given in the
	 * constructor.
	 * 
	 * @param ua - (BCEL) Unknown attribute to load from.
	 * @throws ReadAttributeException - if given attribute's
	 * 		data doesn't represent correct attribute of
	 * 		given attribute's name.
	 */
	public void readAttribute(Unknown ua) throws ReadAttributeException {
		String aname = attrName = ua.getName();
		input = ua.getBytes();
		length = ua.getLength();
		pos = 0;
		if (aname.equals(IDisplayStyle.__mspec)) {
			MLog.putMsg(MLog.PInfo, "    reading attribute: "
					+ IDisplayStyle.__mspec);
			method.setMspec(new MethodSpecification(method, this));
		} else if (aname.equals(IDisplayStyle.__classInvariant)) {
			MLog.putMsg(MLog.PInfo, "    reading attribute: "
					+ IDisplayStyle.__classInvariant);
			bcc.setInvariant(new ClassInvariant(bcc, this));
		} else if (aname.equals(IDisplayStyle.__assertTable)) {
			MLog.putMsg(MLog.PInfo, "    reading attribute: "
					+ IDisplayStyle.__assertTable);
			method.getAmap().getAtab().load(this);
		} else {
			MLog.putMsg(MLog.PTodo, "    unrecognized attribute: " + aname);
			return;
		}
		if (pos != length)
			throw new ReadAttributeException((length - pos) + " of " + length
					+ " bytes unread!");
	}

	/**
	 * Checks that there is enough data left in the
	 * <code>input</code> stream.
	 * 
	 * @param n - number of bytes needed to be avaliable.
	 * @throws ReadAttributeException - if there is less than
	 * 		<code>n</code> bytes left in the stream.
	 */
	private void chkRange(int n) throws ReadAttributeException {
		if (pos + n > length)
			throw new ReadAttributeException("end of input stream in "
					+ attrName + " (size=" + length + ")");
	}

	/**
	 * Reads a byte from <code>input</code> stream.
	 * 
	 * @return read byte.
	 * @throws ReadAttributeException - if there is not enough
	 * 		bytes in the stream to read a byte.
	 */
	public int readByte() throws ReadAttributeException {
		chkRange(1);
		int b = (input[pos] & 0xff);
		pos++;
		return b;
	}

	/**
	 * Reads an short integer (2 bytes) from
	 * <code>input</code> stream.
	 * 
	 * @return read int.
	 * @throws ReadAttributeException - if there is not enough
	 * 		bytes in the stream to read a short integer.
	 */
	public int readShort() throws ReadAttributeException {
		chkRange(2);
		int s = ((input[pos] & 0xff) << 8) + (input[pos + 1] & 0xff);
		pos += 2;
		return s;
	}

	/**
	 * Reads an integer (4 bytes) from <code>input</code>
	 * stream.
	 * 
	 * @return read int.
	 * @throws ReadAttributeException - if there is not enough
	 * 		bytes in the stream to read an int.
	 */
	public int readInt() throws ReadAttributeException {
		chkRange(4);
		int i = (input[pos] & 0xff) << 24;
		i += (input[pos + 1] & 0xff) << 16;
		i += (input[pos + 2] & 0xff) << 8;
		i += input[pos + 3] & 0xff;
		pos += 4;
		return i;
	}

	/**
	 * Reads an attribute count (2 bytes integer) from
	 * <code>input</code> stream.
	 * 
	 * @return read attribute count.
	 * @throws ReadAttributeException - if there is not enough
	 * 		bytes in the stream to read a attribute count.
	 */
	public int readAttributesCount() throws ReadAttributeException {
		return readShort();
	}

	/**
	 * Gives String value of constant with given index, from
	 * constant pool.
	 * 
	 * @param index - index of searched constant.
	 * @return String value of Utf8 constant (from constant
	 * 		pool) of given index.
	 * @throws ReadAttributeException - if there are no Utf8
	 * 		constant at given index in constant pool.
	 */
	public String findString(int index) throws ReadAttributeException {
		Constant c = bcc.getCp().getConstant(index);
		if (c instanceof ConstantUtf8)
			return ((ConstantUtf8) c).getBytes();
		throw new ReadAttributeException("invalid constant index: " + index);
	}

	/**
	 * Reads an expression from <code>input</code> stream.
	 * 
	 * @return Read expression.
	 * @throws ReadAttributeException - if data in the stream
	 * 		doesn't represent correct expression.
	 */
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
		case Code.PLUS:
		case Code.MINUS:
		case Code.MULT:
		case Code.DIV:
		case Code.REM:
		case Code.BITWISEAND:
		case Code.BITWISEOR:
		case Code.BITWISEXOR:
		case Code.SHL:
		case Code.SHR:
		case Code.USHR:
			return new ArithmeticExpression(this, b);
		case Code.NEG:
			return new UnaryArithmeticExpression(this, b);
		case Code.INT_LITERAL:
			return new NumberLiteral(this, b);
		case Code.COND_EXPR:
			return new ConditionalExpression(this, b);
		case Code.NULL:
			return NULL_CLASS.NULL;
		case Code.THIS:
			return bcc.getTHIS(false);
		case Code.OLD_THIS:
			return bcc.getTHIS(true);
		case Code.RESULT:
			return method.getResult();
		case Code.LOCAL_VARIABLE:
			return BCLocalVariable.getLocalVariable(false, method, this);
		case Code.OLD_LOCAL_VARIABLE:
			return BCLocalVariable.getLocalVariable(true, method, this);
		case Code.FIELD_REF:
		case Code.OLD_FIELD_REF:
			return new BCFieldRef(this, b);
		case Code.FIELD_ACCESS:
			return new FieldAccess(this, b);
		case Code.OLD:
			return new OLD(this, b);
		case Code.FORALL:
		case Code.EXISTS:
		case Code.FORALL_WITH_NAME:
		case Code.EXISTS_WITH_NAME:
			return new QuantifiedFormula(this, b);
		case Code.BOUND_VAR:
			return BoundVar.getBoundVar(this);
		case Code.JAVA_TYPE:
			int i = readShort();
			Constant c = bcc.getCp().getConstant(i);
			if (!(c instanceof ConstantUtf8))
				throw new ReadAttributeException(
						"Utf8 expected as javaType name");
			String name = ((ConstantUtf8) c).getBytes();
			return JavaType1.getJavaType(name);
		// TODO: deprecated
		case 0xE1: return new QuantifiedFormula(this, 0x0A);
		case 0xE2: return new QuantifiedFormula(this, 0x0B);
		default:
			throw new ReadAttributeException("Unknown expression code: " + b);
		}
	}
	

	/**
	 * Reads an Expression and checks that it is a formula.
	 * 
	 * @return Read expression.
	 * @throws ReadAttributeException - if data in the stream
	 * 		doesn't represent correct formula.
	 */
	public AbstractFormula readFormula() throws ReadAttributeException {
		BCExpression expr = readExpression();
		if (expr instanceof AbstractFormula) {
			AbstractFormula af = (AbstractFormula) expr;
			return af;
		}
		throw new ReadAttributeException("Formula expected");
	}

	/**
	 * @param index - variable index.
	 * @return Visible bound variable of given index.
	 * @see #bvars
	 */
	public BoundVar getBvar(int index) {
		return bvars.elementAt(index);
	}

	/**
	 * @return Number of currently visible bound variables.
	 */
	public int getBvarCount() {
		return bvars.size();
	}

	/**
	 * @return Currently visible bound variable Vector.
	 */
	public Vector<BoundVar> getBvars() {
		return bvars;
	}

	public BCConstantPool getConstantPool() {
		return bcc.getCp();
	}

}
