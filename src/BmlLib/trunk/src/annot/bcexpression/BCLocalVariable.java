package annot.bcexpression;

import org.apache.bcel.generic.LocalVariableGen;
import annot.bcclass.BCMethod;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents method's local variable.
 * One <code>BCLocalVariable</code> per one local variable.
 * 
 * @author tomekb
 */
public class BCLocalVariable extends OldExpression {

	/**
	 * Method in with this variable has been declared.
	 */
	private BCMethod m;
	
	/**
	 * Number (index) of this variable
	 * in method <code>m</code>.
	 */
	private int lvar_id;
	
	/**
	 * Name of this variable.
	 */
	private String name;
	
	/**
	 * BCEL's representation of this variable.
	 */
	private LocalVariableGen bcelLvGen;
	
	/**
	 * Type of this variable.
	 */
	private JavaType1 type;
	
	/**
	 * A constructor for method initialization only. Later,
	 * use {@link #getLocalVariable(BCMethod, AttributeReader)}
	 * intead.
	 * 
	 * @param m - initializing method,
	 * @param id - number (index) of this local variable
	 * 		in method <code>m</code>,
	 * @param name - name of this variable,
	 * @param lvg - BCEL's representation of this variable.
	 */
	public BCLocalVariable(boolean isOld, BCMethod m, int id, String name,
			LocalVariableGen lvg) {
		super(Code.LOCAL_VARIABLE, isOld);
		this.m = m;
		this.lvar_id = id;
		this.name = name;
		this.bcelLvGen = lvg;
		this.type = JavaType1.convert(lvg.getType());
	}
	
	/**
	 * A 'constructor' from AttributeReader.
	 * 
	 * @param m - method in with variable has been declared,
	 * @param ar - input stream to load from,
	 * @return local variable of index read from
	 * 		<code>ar</code>,
	 * @throws ReadAttributeException - if read index
	 * 		is greater or equal local variable count
	 * 		of method <code>m</code>.
	 */
	public static BCLocalVariable getLocalVariable(
			boolean isOld, BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		int index = ar.readShort() - 1;
		if ((index < 0) || (index >= m.getLocalVariableCount()))
			throw new ReadAttributeException("invalid local variable index: " + index);
		return m.getLocalVariable(isOld, index);
	}
	
	@Override
	protected JavaType1 checkType2() {
		return type;
	}

	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public JavaType1 getType() {
		return type;
	}

	@Override
	protected void init() {}

	@Override
	protected String printCode1(BMLConfig conf) {
		return isOld() ? ("old_" + name) : name;
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new ReadAttributeException("'read' method" +
			" unavaliable, use getLocalVar() instead.");
	}

	@Override
	public String toString() {
		return (isOld() ? "old_" : "") + "lv["+lvar_id+"]";
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(isOld() ? Code.OLD_LOCAL_VARIABLE : Code.LOCAL_VARIABLE);
		aw.writeShort(lvar_id + 1);
	}

	/**
	 * @return variable's name.
	 */
	public String getName() {
		return name;
	}

}
