package annot.attributes;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.textio.BMLConfig;

public abstract class BCPrintableAttribute {

	public String last_code = "";

	public String printCode(BMLConfig conf) {
		last_code = printCode1(conf);
		return last_code;
	}

	protected abstract String printCode1(BMLConfig conf);

	public abstract void replaceWith(BCPrintableAttribute pa);

	public abstract void remove();

	public abstract void parse(String code) throws RecognitionException;

	@Override
	public abstract String toString();

	public void parse(BCClass bcc, BCMethod m, InstructionHandle ih, int minor,
			String code) throws RecognitionException {
		BCPrintableAttribute pa = bcc.parser.parseAttribute(bcc, m, ih, minor,
				code);
		if (pa.getClass() == this.getClass()) {
			replaceWith(pa);
		} else {
			MLog.putMsg(MLog.PNotice, "**** attribute's class changed ****");
			// XXX untested
			remove();
			if (m == null) {
				bcc.addAttribute(pa);
			} else {
				if (pa instanceof MethodSpecification) {
					m.mspec = (MethodSpecification) pa;
				} else if (pa instanceof InCodeAttribute) {
					m.addAttribute((InCodeAttribute) pa);
				} else {
					throw new RuntimeException(
							"(BCPrintableAttribute.parse) Unknown attribute");
				}
			}
		}
	}

}
