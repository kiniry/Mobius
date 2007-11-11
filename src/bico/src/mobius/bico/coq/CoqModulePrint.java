package mobius.bico.coq;

import mobius.bico.executors.Constants;

public class CoqModulePrint {
	
	public static String printReqExport(String module) {
		return Constants.REQ_EXPORT + Constants.SPACE + module +  ".\n"; 
	}
	
	public String printExport(String module) {
		return Constants.EXPORT + Constants.SPACE +  module +  ".\n"; 
	}
	
	public String printReqImport(String module) {
		return Constants.REQ_IMPORT + Constants.SPACE + module +  ".\n"; 
	}
	
	public String printImport(String module) {
		return Constants.IMPORT + Constants.SPACE +  module +  ".\n"; 
	}
	
	
}
