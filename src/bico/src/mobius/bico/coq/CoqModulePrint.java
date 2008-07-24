package mobius.bico.coq;

import mobius.bico.executors.Constants.Syntax;

class CoqModulePrint {  
  public static String printReqExport(String module) {
  	return Syntax.REQ_EXPORT + module +  ".\n"; 
  }
  
  public String printExport(String module) {
  	return Syntax.EXPORT + module +  ".\n"; 
  }
  
  public String printReqImport(String module) {
  	return Syntax.REQ_IMPORT + module +  ".\n"; 
  }
  
  public String printImport(String module) {
  	return Syntax.IMPORT + module +  ".\n"; 
  }
  

}
