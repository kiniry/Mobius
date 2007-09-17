package annot.attributes;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public abstract class InCodeAttribute extends BCPrintableAttribute implements
		Comparable<InCodeAttribute> {

	private BCMethod method;
	private InstructionHandle ih;
	private int minor;

	public InCodeAttribute(BCMethod m, InstructionHandle ih, int minor) {
		this.method = m;
		this.ih = ih;
		this.minor = minor;
	}

	@Deprecated
	public InCodeAttribute(BCMethod m, int pc, int minor) {
		this(m, m.findAtPC(pc), minor);
	}

	public abstract void load(AttributeReader ar) throws ReadAttributeException;

	public abstract void saveSingle(AttributeWriter aw);

	public abstract int aType();

	@Override
	public abstract String printCode1(BMLConfig conf);

	@Override
	public void replaceWith(BCPrintableAttribute pa) {
		InCodeAttribute ica = (InCodeAttribute) pa;
		if (ica.ih == null) {
			ica.ih = ih;
			ica.minor = minor;
		}
		method.getAmap().replaceAttribute(this, ica);
	}

	@Override
	public void parse(String code) throws RecognitionException {
		parse(method.getBcc(), method, ih, minor, code);
	}

	public int getPC() {
		method.getInstructions().setPositions();
		return ih.getPosition();
	}

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

	public InstructionHandle getIh() {
		return ih;
	}

	protected void setIh(InstructionHandle ih) {
		this.ih = ih;
	}

	public BCMethod getMethod() {
		return method;
	}

	public int getMinor() {
		return minor;
	}

	protected void setMinor(int minor) {
		this.minor = minor;
	}

}
