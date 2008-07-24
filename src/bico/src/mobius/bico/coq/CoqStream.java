package mobius.bico.coq;

import java.io.OutputStream;

import mobius.bico.executors.Constants.Syntax;

/**
 * A Stream that permits to write some coq specific syntax.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CoqStream extends Stream {
  /**
   * It builds the stream from a normal output stream.
   * @param out the output stream that will be written to
   */
  public CoqStream(final OutputStream out) {
    super(out);
  }
  
  /**
   * Prints "<code>Add LoadPath module.</code>".
   * @param module the module name
   */
  public void addLoadPath(final String module) {
    println(Syntax.ADD_LOAD_PATH + "\"" + module +  "\"."); 
  }
  
  /**
   * Prints "<code>Load module.</code>".
   * @param module the module name
   */
  public void load(final String module) {
    println(Syntax.LOAD + "\"" + module +  "\"."); 
  }

  /**
   * Prints "<code>Require Import module.</code>".
   * @param module the module name
   */
  public void reqImport(final String module) {
    println(Syntax.REQ_IMPORT + module +  "."); 
  }
  
  /**
   * Prints "<code>Require Export module.</code>".
   * @param module the module name
   */
  public void reqExport(final String module) {
    println(Syntax.REQ_EXPORT + module +  "."); 
  }
  
  /**
   * Prints "<code>Export module.</code>".
   * @param module the module name
   */
  public void exprt(final String module) {
    println(Syntax.EXPORT + module +  "."); 
  }
  
  /**
   * Prints "<code>Require Import module.</code>".
   * @param module the module name
   */
  public void imprt(final String module) {
    println(Syntax.IMPORT + module +  "."); 
  }
  
  /**
   * Prints "<code>Module module.</code>" and
   * increments the following lines of one tab.
   * 
   * @param module the module name
   */
  public void startModule(final String module) {
    incPrintln(Syntax.MODULE + module +  "."); 
  }
  
  /**
   * Decrements of one tab and then print
   *  "<code>End module.</code>".
   * 
   * @param module the module name
   */
  public void endModule(final String module) {
    decPrintln(Syntax.END_MODULE + module +  "."); 
  }
}
