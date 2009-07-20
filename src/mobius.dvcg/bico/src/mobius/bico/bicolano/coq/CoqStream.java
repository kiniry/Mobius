package mobius.bico.bicolano.coq;

import java.io.File;
import java.io.OutputStream;

import mobius.bico.bicolano.Stream;
import mobius.bico.bicolano.coq.Translator.Syntax;


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
   * Prints "<code>Add LoadPath path.\n</code>".
   * @param path the path name
   */
  public void addLoadPath(final LoadPath path) {
    println(Translator.addLoadPath(path));
  }
  
  /**
   * Prints "<code>Add LoadPath module.\n</code>".
   * @param path the path name
   * @param relativeTo the path the main path is relative to
   */
  public void addLoadPath(final LoadPath path, 
                          final File relativeTo) {
    println(Translator.addLoadPath(path, relativeTo));
  }
  
  /**
   * Prints "<code>Load module.\n</code>".
   * @param module the module name
   */
  public void load(final String module) {
    println(Syntax.LOAD + "\"" + module +  "\"."); 
  }

  /**
   * Prints "<code>Require Import module.\n</code>".
   * @param module the module name
   */
  public void reqImport(final String module) {
    println(Translator.reqImport(module)); 
  }
  
  /**
   * Prints "<code>Require Export module.\n</code>".
   * @param module the module name
   */
  public void reqExport(final String module) {
    println(Translator.reqExport(module)); 
  }
  
  /**
   * Prints "<code>Export module.\n</code>".
   * @param module the module name
   */
  public void exprt(final String module) {
    println(Translator.exprt(module)); 
  }
  
  /**
   * Prints "<code>Import module.\n</code>".
   * @param module the module name
   */
  public void imprt(final String module) {
    println(Translator.imprt(module)); 
  }
  
  /**
   * Prints "<code>Module module.\n</code>" and
   * increments the following lines of one tab.
   * 
   * @param module the module name
   */
  public void startModule(final String module) {
    incPrintln(Syntax.MODULE + module +  "."); 
  }
  
  /**
   * Decrements of one tab and then print
   *  "<code>End module.\n</code>".
   * 
   * @param module the module name
   */
  public void endModule(final String module) {
    decPrintln(Syntax.END_MODULE + module +  "."); 
  }
  /**
   * Prints "<code>Definition name := </code>".
   * @param name the name of the definition
   */
  public void definitionStart(final String name) {
    definitionStart(name, null);
  }
  
  /**
   * Prints "<code>Definition name: type := </code>".
   * @param name the name of the definition
   * @param type  the type of the definition
   */
  public void definitionStart(final String name, final String type) {
    String s = Syntax.DEFINITION + name;
    if (type != null && !type.equals("")) {
      s += ": " + type;
    }
    s += " := ";
    print(s);
  }
  
  /**
   * Prints "<code>Definition name: type := body.\n</code>".
   * @param name the name of the definition
   * @param type  the type of the definition
   * @param body the body of the definition
   */
  public void definition(final String name, final String type, final String body) {
    definitionStart(name, type);
    println(body + ".");
  }
  
  /**
   * Prints "<code>Definition name := body.\n</code>".
   * @param name the name of the definition
   * @param body the body of the definition
   */
  public void definition(final String name, final String body) {
    definition(name, null, body);
  }
  
  
}
