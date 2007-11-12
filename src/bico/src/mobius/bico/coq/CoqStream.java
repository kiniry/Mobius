package mobius.bico.coq;

import java.io.OutputStream;

import mobius.bico.executors.Constants;


public class CoqStream extends Stream {

  public CoqStream(OutputStream out) {
    super(out);
  }

  public void reqImport(String module) {
    println(Constants.REQ_IMPORT + module +  "."); 
  }
  public void reqExport(String module) {
    println(Constants.REQ_EXPORT + module +  "."); 
  }
  
  public void exprt(String module) {
    println(Constants.EXPORT + module +  "."); 
  }
  
  public void imprt(String module) {
    println(Constants.IMPORT + module +  "."); 
  }
  public void startModule(String module) {
    incPrintln(Constants.MODULE + module +  "."); 
  }
  public void endModule(String module) {
    decPrintln(Constants.END_MODULE + module +  "."); 
  }
}