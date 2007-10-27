package annot.attributes;

import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.modifies.ModifyList;
import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

/**
 * This class represents single loop specification annotation
 * (on or more InCodeAttribute per one bytecode instruction) 
 * 
 * @author tomekb
 */
public class SingleLoopSpecification extends InCodeAttribute {

	/**
	 * list of variables that can be affected by specified
	 * loop.
	 */
	private ExpressionRoot<ModifyList> modifies;
	
	/**
	 * a loop's invariant.
	 */
	private ExpressionRoot<BCExpression> invariant;
	
	/**
	 * a loop variant.
	 */
	private ExpressionRoot<BCExpression> decreases;

	/**
	 * A standard constructor.
	 * 
	 * @param m - BCMethod containing this annotation,
	 * @param ih - instructionHandle of bytecode instruction
	 * 		that this annotation should be attached to,
	 * @param minor - minor number of annotation, responsible
	 * 		for annotation ordering within single instruction,
	 * @param modifies - list of variables that can
	 * 		be affected by specified loop,
	 * @param invariant - loop's invariant,
	 * @param decreases - loop's variant.
	 */
	public SingleLoopSpecification(BCMethod m,
			InstructionHandle ih, int minor,
			ModifyList modifies, BCExpression invariant,
			BCExpression decreases) {
		super(m, ih, minor);
		if (modifies == null)
			modifies = new ModifyList();
		if (invariant == null)
			invariant = Predicate0Ar.TRUE;
		if (decreases == null)
			decreases = new NumberLiteral(1);
		this.modifies = new ExpressionRoot<ModifyList>(this, modifies);
		this.invariant = new ExpressionRoot<BCExpression>(this, invariant);
		this.decreases = new ExpressionRoot<BCExpression>(this, decreases);
	}

	@Override
	protected int aType() {
		return AType.C_LOOPSPEC;
	}

	@Override
	protected void load(AttributeReader ar) throws ReadAttributeException {
		this.modifies = new ExpressionRoot<ModifyList>(this, new ModifyList(ar));
		this.invariant = new ExpressionRoot<BCExpression>(this, ar.readExpression());
		this.decreases = new ExpressionRoot<BCExpression>(this, ar.readFormula());
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		String code = IDisplayStyle._loopspec;
		conf.incInd();
		code += conf.nl() + modifies.printLine(conf, IDisplayStyle._loop_modifies);
		code += conf.nl() + invariant.printLine(conf, IDisplayStyle._loop_invariant);
		code += conf.nl() + decreases.printLine(conf, IDisplayStyle._loop_decreases);
		conf.decInd();
		return code;
	}

	@Override
	protected void saveSingle(AttributeWriter aw) {
		modifies.write(aw);
		invariant.write(aw);
		decreases.write(aw);
	}

	@Override
	public ExpressionRoot[] getAllExpressions() {
		ExpressionRoot[] all = new ExpressionRoot[3];
		all[0] = modifies;
		all[1] = invariant;
		all[2] = decreases;
		return all;
	}

	@Override
	public String toString() {
		return "loop spec. at (" + getPC() + ", "
		+ ((getMinor() == -1) ? "any" : getMinor()) + ")";
	}

}
