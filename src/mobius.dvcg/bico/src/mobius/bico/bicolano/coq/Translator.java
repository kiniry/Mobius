package mobius.bico.bicolano.coq;

import java.io.File;


import org.apache.bcel.classfile.AccessFlags;

/**
 * This utility class is used to translate some
 * of the Coq syntax to string.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class Translator {
  
  /** */
  private Translator() { }
  
  /**
   * Returns a couple "<code>(elem1, elem2)</code>".
   * @param elem1 the first element of the couple
   * @param elem2 the second element of the couple
   * @return a string representing the couple
   */
  public static String couple(final String elem1, 
                              final String elem2) {
    return "(" + elem1 + ", " + elem2 + ")";
  }
  
  /**
   * for printing offsets.
   * 
   * @param index
   *            the offset to print
   * @return i%Z or (-i)%Z
   */
  public static String toZ(final Number index) {
    return toZ(index.intValue());
  }
  
  /**
   * for printing offsets.
   * 
   * @param index
   *            the offset to print
   * @return i%Z or (-i)%Z
   */
  public static String toZ(final int index) {
    if (index < 0) {
      return "(" + index + ")%Z";
    } 
    else {
      return String.valueOf(index) + "%Z";
    }
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
    ADD_LOAD_PATH("Add LoadPath "),
    /** corresponds to the string "(* ". */ 
    LCOMMENT("(* "),  
    /** corresponds to the string " *)". */ 
    RCOMMENT(" *)");
    
    
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
   * Java Access representation.
   * Access is Private, Protected, etc...
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static enum Access {
    /** the private access. */
    PRIVATE("Private"),
    /** the protected access. */
    PROTECTED("Protected"),
    /** the public access. */
    PUBLIC("Public"),
    /** the package access. */
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
    
    /**
     * Translate an access flags structure to an access
     * constant.
     * @param af the access flags
     * @return an instance of acces: private, protected, etc...
     */
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

  /**
   * @return "<code>Require Import module.</code>"
   * @param module the module name
   */
  public static String reqImport(final String module) {
    return Syntax.REQ_IMPORT + module +  "."; 
  }
  
  /**
   * @return "<code>Require Export module.</code>"
   * @param module the module name
   */
  public static String reqExport(final String module) {
    return Syntax.REQ_EXPORT + module +  "."; 
  }
  
  /**
   * @return "<code>Export module.</code>"
   * @param module the module name
   */
  public static String exprt(final String module) {
    return Syntax.EXPORT + module +  "."; 
  }
  
  /**
   * @return "<code>Import module.</code>"
   * @param module the module name
   */
  public static String imprt(final String module) {
    return Syntax.IMPORT + module +  "."; 
  }
  /**
   * @return "<code>Add LoadPath path.</code>".
   * @param path the path name
   * @deprecated use {@link #addLoadPath(LoadPath)} instead
   */
  public static String addLoadPath(final String path) {
    return addLoadPath(new LoadPath(path)); 
  }
  
  /**
   * @return "<code>Add LoadPath path.</code>".
   * @param path the path name
   */
  public static String addLoadPath(final LoadPath path) {
    return Syntax.ADD_LOAD_PATH + "\"" + path +  "\"."; 
  }
  
  /**
   * @return "<code>Add LoadPath module.</code>".
   * @param path the path name
   * @param relativeTo the path the main path is relative to
   */
  public static String addLoadPath(final LoadPath path, 
                          final File relativeTo) {
    return addLoadPath(new LoadPath(path.getRelative(relativeTo))); 
  }
  
  /**
   * @param str the string to put in the comments
   * @return "<code>(* str *)</code>"
   */
  public static String comment(final String str) {
    return Syntax.LCOMMENT + str + Syntax.RCOMMENT;
  }
}
