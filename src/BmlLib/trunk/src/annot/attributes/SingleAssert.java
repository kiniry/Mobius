package annot.attributes;

import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.formula.AbstractFormula;
import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

public class SingleAssert extends InCodeAttribute {

	private AbstractFormula formula;

	public SingleAssert(BCMethod m, InstructionHandle ih, int minor) {
		super(m, ih, minor);
		this.formula = Predicate0Ar.TRUE;
	}

	public SingleAssert(BCMethod m, InstructionHandle ih, int minor,
			AbstractFormula formula) {
		super(m, ih, minor);
		this.formula = formula;
	}

	@Deprecated
	public SingleAssert(BCMethod m, int pc, int minor, AbstractFormula f) {
		super(m, pc, minor);
		this.formula = f;
	}

	@Deprecated
	public SingleAssert(BCMethod m, int pc, int minor) {
		super(m, pc, minor);
		this.formula = Predicate0Ar.TRUE;
	}

	@Override
	public void load(AttributeReader ar) throws ReadAttributeException {
		formula = (AbstractFormula) ar.readExpression();
	}

	@Override
	public String printCode1(BMLConfig conf) {
		return formula.printLine(conf, IDisplayStyle._assert);
	}

	@Override
	public void saveSingle(AttributeWriter aw) {
		formula.write(aw);
	}

	@Override
	public void remove() {
		getMethod().getAmap().removeAttribute(this);
	}

	@Override
	public int aType() {
		return AType.C_ASSERT;
	}

	@Override
	public String toString() {
		return "assert at (" + getPC() + ", " + ((getMinor() == -1) ? "any" : getMinor())
				+ ")";
	}

	public AbstractFormula getFormula() {
		return formula;
	}

	public void setFormula(AbstractFormula formula) {
		this.formula = formula;
	}

}
