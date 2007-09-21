package annot.attributes;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents single annotations attached to
 * instructionHandle of an bytecode instruction.
 * (on or more InCodeAttribute per one bytecode instruction) 
 * 
 * @author tomekb
 */
public abstract class InCodeAttribute extends BCPrintableAttribute implements
		Comparable<InCodeAttribute> {

	/**
	 * The method containing this annotation.
	 */
	private BCMethod method;

	/**
	 * InstructionHandle of bytecode instruction that this
	 * annotation is attached to.
	 * Changed from pc number of instruction to avoid
	 * desynchronization after inserting / deleting bytecode
	 * instructions above.   
	 */
	private InstructionHandle ih;

	/**
	 * This number is responsible for annotation ordering
	 * within single bytecode instruction.
	 * Multiple annotations can be attached to one instruction.
	 * They are sorted by thier minor number and displayed
	 * in this order.
	 */
	private int minor;

	/**
	 * A standard constructor.
	 * 
	 * @param m - BCMethod containing this annotation,
	 * @param ih - instructionHandle of bytecode instruction
	 * 		that this annotation should be attached to,
	 * @param minor - minor number of annotation, responsible
	 * 		for annotation ordering within single instruction.
	 */
	public InCodeAttribute(BCMethod m, InstructionHandle ih, int minor) {
		this.method = m;
		this.ih = ih;
		this.minor = minor;
	}

	/**
	 * A constructor for tests only. It can be used only
	 * when we are sure that bytecode itself won't change.
	 * 
	 * @param m - BCMethod containing this annotation,
	 * @param pc - pc number of bytecode instruction that
	 * 		this annotation should be attached to. You should
	 * 		be sure that instruction of that pc really
	 * 		exists in given method.
	 * @param minor - minor number of annotation, responsible
	 * 		for annotation ordering within single instruction.
	 */
	@Deprecated
	public InCodeAttribute(BCMethod m, int pc, int minor) {
		this(m, m.findAtPC(pc), minor);
	}

	/**
	 * Loads annotation's content from AttributeReader.
	 * 
	 * @param ar - stream to load from.
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent correct
	 * 		annotation.
	 */
	protected abstract void load(AttributeReader ar) throws ReadAttributeException;

	/**
	 * Saves annotation content using AttributeWriter.
	 * 
	 * @param aw - stream to save to.
	 */
	protected abstract void saveSingle(AttributeWriter aw);

	/**
	 * This method should simply print annotation to a string.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return string representation of annotation.
	 */
	@Override
	protected abstract String printCode1(BMLConfig conf);

	/**
	 * @return annotation's type id, from AType interface.
	 */
	protected abstract int aType();

	/**
	 * Replaces this annotation with a given one, updating
	 * nessesery references in BCAttributeMap in BCMethod.
	 * 
	 * @param pa - annotation to replace with.
	 */
	@Override
	public void replaceWith(BCPrintableAttribute pa) {
		InCodeAttribute ica = (InCodeAttribute) pa;
		if (ica.ih == null) {
			ica.ih = ih;
			ica.minor = minor;
		}
		method.getAmap().replaceAttribute(this, ica);
	}

	/**
	 * Removes this annotation.
	 */
	@Override
	public void remove() {
		getMethod().getAmap().removeAttribute(this);
	}

	/**
	 * Replaces this annotation with the one parsed from
	 * given String.
	 * 
	 * @param code - correct code of annotation
	 * 		to replace with.
	 * @throws RecognitionException - if <code>code</code>
	 * 		is not correct annotation's code.
	 */
	@Override
	public void parse(String code) throws RecognitionException {
		parse(method.getBcc(), method, ih, minor, code);
	}

	/**
	 * Computes pc numbers for each bytecode instruction of
	 * a method containing this annotation and returns,
	 * and returns pc number of instruction this annotation
	 * is attached to.
	 * 
	 * @return pc number of this annotation's
	 * 		bytecode instruction.
	 */
	public int getPC() {
		method.getInstructions().setPositions();
		return ih.getPosition();
	}

	/**
	 * compares this annotation to given one in order they
	 * should appead in String representation of a method.
	 * Both annotations should be from the same method.
	 * @param o - annotation to compare to.
	 * @return a positive integer if <code>o</code> is above
	 * 		this annotation in String representation of method,
	 * 		a negative integer if <code>o</code> is below,
	 * 		and zero if <code>o</code> is the same annotation.
	 */
	public int compareTo(InCodeAttribute o) {
		int pc = getPC();
		int opc = o.getPC();
		if (pc == opc) {
			if (minor == o.minor) {
				return 0;
			} else {
				return minor - o.minor;
			}
		} else {
			return pc - opc;
		}
	}

	/**
	 * @return instructionHandle of instruction this annotation
	 * 		is attached to.
	 */
	public InstructionHandle getIh() {
		return ih;
	}

	/**
	 * Sets instructionHandle parameter.
	 * 
	 * @param ih - new instruction handle.
	 */
	protected void setIh(InstructionHandle ih) {
		this.ih = ih;
	}

	/**
	 * @return BCMethod containing this annotation.
	 */
	public BCMethod getMethod() {
		return method;
	}

	/**
	 * @return minor number of this annotation, used for
	 * 		ordering annotations within the same bytecode
	 * 		instruction.
	 */
	public int getMinor() {
		return minor;
	}

	/**
	 * Sets minor number.
	 * 
	 * @param minor - new minor number value to set.
	 */
	protected void setMinor(int minor) {
		this.minor = minor;
	}

}
