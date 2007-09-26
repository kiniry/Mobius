package annot.textio;

import org.antlr.runtime.RecognitionException;

import annot.attributes.BCPrintableAttribute;
import annot.attributes.InCodeAttribute;
import annot.attributes.SingleList;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;

public class CodeFragment {

	public static final int RANGE_CLASS = 3;
	public static final int RANGE_METHOD = 2;
	public static final int RANGE_INSTRUCTION = 1;
	public static final int RANGE_ANNOT = 0;
	
	private BCClass bcc;
	private String code;
	private int begin;
	private int end;
	private Parsing parser;
	private String prefix;
	private String suffix;
	private BCPrintableAttribute attr;
	private SingleList instr;
	private BCMethod method;
	private int range = -1;
	
	public CodeFragment(BCClass bcc, String code, int cfrom, int cto) {
		this.bcc = bcc;
		this.code = code;
		this.begin = cfrom;
		this.end = cto;
		this.parser = bcc.getParser();
		init();
	}
	
	private void init() {
		//TODO
	}
	
	public boolean parse(String newCode) {
		try {
			String s_code = prefix + newCode + suffix;
			if (attr != null) {
				attr.parse(s_code);
			} else if (instr != null) {
				String[] all = CodeSearch.getAllAttributeNames();
				String or = "[";
				for (int i=0; i<all.length; i++) {
					if (i > 0)
						or += "|";
					or += Parsing.escape(all[i]);
				}
				or += ']';
				String[] acodes = s_code.split(or);
				int n = acodes.length;
				InCodeAttribute[] newAttrs = new InCodeAttribute[n];
				for (int i=0; i<n; i++) {
					String acode = Parsing.purge(acodes[i]);
					BCPrintableAttribute pa = parser.parseAttribute(
						method, instr.getIh(), i, acode);
					if (!(pa instanceof InCodeAttribute))
						throw new RecognitionException();
					newAttrs[i] = (InCodeAttribute)pa;
				}
				instr.removeAll();
				for (int i=0; i<n; i++)
					instr.addAttribute(newAttrs[i]);
			} else if (method != null) {
				MLog.putMsg(MLog.PTodo, "Method updating unimplemented!");
				return false;
				//TODO
			} else {
				MLog.putMsg(MLog.PTodo, "Class updating unimplemented!");
				return false;
				//TODO
			}
		} catch (RecognitionException e) {
			return false;
		}
		return true;
	}
	
	public int getRange() {
		return range;
	}
}
