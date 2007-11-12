package mobius.bico.coq;

import mobius.bico.executors.Constants;

class CoqModulePrint {  
  public static String printReqExport(String module) {
  	return Constants.REQ_EXPORT + module +  ".\n"; 
  }
  
  public String printExport(String module) {
  	return Constants.EXPORT + module +  ".\n"; 
  }
  
  public String printReqImport(String module) {
  	return Constants.REQ_IMPORT + module +  ".\n"; 
  }
  
  public String printImport(String module) {
  	return Constants.IMPORT + module +  ".\n"; 
  }
  

}
