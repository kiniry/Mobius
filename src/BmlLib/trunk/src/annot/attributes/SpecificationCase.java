package annot.attributes;

import java.util.Iterator;
import java.util.Vector;

import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.modifies.ModifyExpression;
import annot.bcexpression.modifies.ModifyList;
import annot.formula.AbstractFormula;
import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

/**
 * This class represents single specification case
 * of method specification.
 * 
 * @author tomekb
 */
public class SpecificationCase {

	/**
	 * A method this specificationCase specifies.
	 */
	private BCMethod method;

	/**
	 * This case should be considered only if its precondition
	 * evaluates to true.
	 */
	private ExpressionRoot<AbstractFormula> precondition;

	/**
	 * This expression describes what variables can change
	 * in this case.
	 */
	private ExpressionRoot<ModifyList> modifies;

	/**
	 * A condition that should be true if precondition is so.
	 */
	private ExpressionRoot<AbstractFormula> postcondition;

	/**
	 * exception conditions vector. Each element describes
	 * on of exception throws by described method.
	 */
	private Vector<Exsure> excondition;
	
	/**
	 * Creates an empty specification case, with both
	 * precondition and postcondition set to true.
	 * 
	 * @param m - a method this specificationCase specifies.
	 */
	public SpecificationCase(BCMethod m) {
		this.method = m;
		this.precondition = new ExpressionRoot<AbstractFormula>(this, new Predicate0Ar(true));
		this.modifies = new ExpressionRoot<ModifyList>(this, new ModifyList());
		this.postcondition = new ExpressionRoot<AbstractFormula>(this, new Predicate0Ar(true));
		this.excondition = new Vector<Exsure>();
	}

	/**
	 * A standard constructor.
	 * 
	 * @param m - a method this specificationCase specifies.
	 * @param precondition - specification case's precondition,
	 * @param postcondition - specification case's
	 * 		postcondition.
	 */
	public SpecificationCase(BCMethod m, AbstractFormula precondition,
			ModifyList modifies, AbstractFormula postcondition,
			Vector<Exsure> exsures) {
		this.method = m;
		if (precondition == null)
			throw new RuntimeException("SpecificationCase's precondition == null !");
		this.precondition = new ExpressionRoot<AbstractFormula>(this, precondition);
		if (modifies == null)
			modifies = new ModifyList();
		this.modifies = new ExpressionRoot<ModifyList>(this, modifies);
		if (postcondition == null)
			postcondition = new Predicate0Ar(true);
		this.postcondition = new ExpressionRoot<AbstractFormula>(this, postcondition);
		if (exsures == null)
			exsures = new Vector<Exsure>();
		this.excondition = exsures;
	}

	/**
	 * A constructor from AttributeReader, used only for
	 * loading specification case from .class file.
	 * 
	 * @param m - method this annotation specifies.
	 * @param ar - stream to load from.
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent correct
	 * 		specification case.
	 */
	public SpecificationCase(BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		this(m);
		this.precondition = new ExpressionRoot<AbstractFormula>(this, ar.readFormula());
		this.modifies = new ExpressionRoot<ModifyList>(this, new ModifyList(ar));
		this.postcondition = new ExpressionRoot<AbstractFormula>(this, ar.readFormula());
		this.excondition = new Vector<Exsure>();
		int count = ar.readAttributesCount();
		for (int i=0; i<count; i++) {
			Exsure ex = new Exsure(ar);
			excondition.add(ex);
		}
	}

	/**
	 * Saves specification case using AttributeWriter.
	 * 
	 * @param aw - stream to save to.
	 */
	public void write(AttributeWriter aw) {
		precondition.write(aw);
		modifies.write(aw);
		postcondition.write(aw);
		aw.writeAttributeCount(excondition.size());
		Iterator<Exsure> iter = excondition.iterator();
		while (iter.hasNext())
			iter.next().writeSingle(aw);
	}

	/**
	 * Prints specification case to a string.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return string representation of specificatoin case.
	 */
	public String printCode(BMLConfig conf) {
		String code = " ";
		code += IDisplayStyle._sc_start + conf.newLine();
		conf.incInd();
		code += precondition.printLine(conf, IDisplayStyle._precondition);
		if (!modifies.getExpression().isEmpty())
			code += modifies.printLine(conf, IDisplayStyle._modifies);
		code += postcondition.printLine(conf, IDisplayStyle._postcondition);
		if (excondition.size() == 1) {
			code += conf.getIndent() + IDisplayStyle._exsures + excondition.get(0).printCode(conf);
		} else if (excondition.size() > 1) {
			code += conf.getIndent() + IDisplayStyle._exsures;
			Iterator<Exsure> iter = excondition.iterator();
			while (iter.hasNext()) {
				code += conf.newLine();
				code += iter.next().printCode(conf);
			}
			conf.decInd();
			code += conf.newLine();
			conf.incInd();
		}
		conf.decInd();
		code += " " + IDisplayStyle._sc_end + conf.newLine();
		return code;
	}

	/**
	 * @return number of expressions (not recursivly) in this
	 * 		attribute (including expressions (postconditions)
	 * 		in excondition).
	 */
	public int getExprCount() {
		int n = 0;
		if (precondition != null) n++;
		if (modifies != null) n++;
		if (postcondition != null) n++;
		if (excondition != null)
			n += excondition.size();
		return n;
	}
	
	/**
	 * @return Array of expressions (not recursivly) in this
	 * 		attribute (including expressions (postconditions)
	 * 		in excondition).
	 */
	public ExpressionRoot[] getAllExpressions() {
		int n = getExprCount();
		ExpressionRoot[] all = new ExpressionRoot[n];
		int pos = 0;
		if (precondition != null)
			all[pos++] = precondition;
		if (modifies != null)
			all[pos++] = modifies;
		if (postcondition != null)
			all[pos++] = postcondition;
		if (excondition != null)
			for (int i=0; i<excondition.size(); i++)
				all[pos++] = excondition.get(i).getPostcondition();
		return all;
	}

}
