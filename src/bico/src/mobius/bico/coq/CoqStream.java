package mobius.bico.coq;

import java.io.File;
import java.io.OutputStream;

import org.apache.bcel.classfile.AccessFlags;


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
    println(Syntax.ADD_LOAD_PATH + "\"" + path +  "\"."); 
  }
  
  /**
   * Prints "<code>Add LoadPath module.\n</code>".
   * @param path the path name
   * @param relativeTo the path the main path is relative to
   */
  public void addLoadPath(final LoadPath path, 
                          final File relativeTo) {
    addLoadPath(new LoadPath(path.getRelative(relativeTo))); 
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
    println(Syntax.REQ_IMPORT + module +  "."); 
  }
  
  /**
   * Prints "<code>Require Export module.\n</code>".
   * @param module the module name
   */
  public void reqExport(final String module) {
    println(Syntax.REQ_EXPORT + module +  "."); 
  }
  
  /**
   * Prints "<code>Export module.\n</code>".
   * @param module the module name
   */
  public void exprt(final String module) {
    println(Syntax.EXPORT + module +  "."); 
  }
  
  /**
   * Prints "<code>Require Import module.\n</code>".
   * @param module the module name
   */
  public void imprt(final String module) {
    println(Syntax.IMPORT + module +  "."); 
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
   * Prints "<code>Definition name: type := body.</code>".
   * @param name the name of the definition
   * @param type  the type of the definition
   * @param body the body of the definition
   */
  public void definition(final String name, final String type, final String body) {
    definitionStart(name, type);
    println(body + ".");
  }
  
  /**
   * Prints "<code>Definition name := body.</code>".
   * @param name the name of the definition
   * @param body the body of the definition
   */
  public void definition(final String name, final String body) {
    definition(name, null, body);
  }
  
  /**
   * Elements of Coq syntax.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static enum Syntax {
    /** corresponds to the string "Module ". */ 
    MODULE("Module "),
    /** corresponds to the string "Load ". */ 
    LOAD("Load "),
    /** corresponds to the string "End ". */ 
    END_MODULE("End "),
    /** corresponds to the string "Require Export ". */ 
    REQ_EXPORT("Require Export "),
    /** corresponds to the string "Export ". */ 
    EXPORT("Export "),
    /** corresponds to the string "Require Import ". */ 
    REQ_IMPORT("Require Import "),
    /** corresponds to the string "Import ". */ 
    IMPORT("Import "),
    /** corresponds to the string "Definition ". */ 
    DEFINITION("Definition "),
    /** corresponds to the string "End ". */ 
    END_DEFINITION("End "),
    /** corresponds to the string "Add LoadPath ". */ 
    ADD_LOAD_PATH("Add LoadPath ");
    
    
    
    /** the string representing the keyword. */
    private final String fStr;
    
    /**
     * Constructs the constant, using the string to initialize it.
     * @param str the string representing the option.
     */
    private Syntax(final String str) {
      fStr = str;
    }
    
    /** {@inheritDoc} */
    public String toString() {
      return fStr;
    }
  }
  /**
   * Elements of Coq syntax.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static enum Access {
    
    PRIVATE("Private"),
    PROTECTED("Protected"),
    PUBLIC("Public"),
    PACKAGE("Package");
    
    /** the string representing the coq version of the access flag. */
    private final String fStr;
    
    /**
     * Constructs the access element, using the string to initialize it.
     * @param str the string representing the option.
     */
    private Access(final String str) {
      fStr = str;
    }
    
    /** {@inheritDoc} */
    public String toString() {
      return fStr;
    }
    
    public static Access translate(final AccessFlags af) {
      final Access res;
      if (af.isPrivate()) {
        res = PRIVATE;
      } 
      else if (af.isProtected()) {
        res = PROTECTED;
      } 
      else if (af.isPublic()) {
        res = PUBLIC;
      } 
      else {
        res = PACKAGE;
      }
      return res;
    }
  }
}
