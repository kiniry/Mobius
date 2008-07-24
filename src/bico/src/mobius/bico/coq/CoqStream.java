package mobius.bico.coq;

import java.io.OutputStream;

import mobius.bico.executors.Constants.Syntax;


public class CoqStream extends Stream {

  public CoqStream(OutputStream out) {
    super(out);
  }
  
  public void addLoadPath(String module) {
    println(Syntax.ADD_LOAD_PATH + "\"" + module +  "\"."); 
  }
  
  public void load(String module) {
    println(Syntax.LOAD + "\"" + module +  "\"."); 
  }

  public void reqImport(String module) {
    println(Syntax.REQ_IMPORT + module +  "."); 
  }
  
  public void reqExport(String module) {
    println(Syntax.REQ_EXPORT + module +  "."); 
  }
  
  public void exprt(String module) {
    println(Syntax.EXPORT + module +  "."); 
  }
  
  public void imprt(String module) {
    println(Syntax.IMPORT + module +  "."); 
  }
  public void startModule(String module) {
    incPrintln(Syntax.MODULE + module +  "."); 
  }
  public void endModule(String module) {
    decPrintln(Syntax.END_MODULE + module +  "."); 
  }
}
