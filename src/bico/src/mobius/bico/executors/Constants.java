package mobius.bico.executors;

/**
 * This class is used as a library to handle constants.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class Constants {
  /** the separator for the packages. */
  public static final char JAVA_NAME_SEPARATOR = '.';
  /** the class suffix. */
  public static final String CLASS_SUFFIX = ".class";
  
  /**
   * Constants representing options passed to  
   * the entry point.
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static enum Option {
    /** to have the map implementation. */
    MAP("-map"),
    /** to have the list implementation. */
    LIST("-list"),
    /** the base working class path. */
    CLASSPATH("-cp"),
    /** the output directory. */
    OUTPUT("-o"),
    /** to show the help message. */
    HELP("-help"),
    /** to tell the location of the bicolano jar. */
    LIB("-lib"), 
    /** the option if all else fails. */
    UNKNOWN(""); 
    
    /** the string representing the option. */
    private final String fStr;
    
    /**
     * Constructs the constant, using the string to initialize it.
     * @param str the string representing the option.
     */
    private Option(final String str) {
      fStr = str;
    }
    
    /** {@inheritDoc} */
    public String toString() {
      return fStr;
    }

    /**
     * Translates an option string to a valid option.
     * @param arg the option string
     * @return an option constant
     */
    public static Option translate(final String arg) {
      Option res = UNKNOWN;
      
      if (arg.equals(HELP.fStr)) {
        res = HELP;
      } 
      else if (arg.equals(LIST.fStr)) {
        res = LIST;
      } 
      else if (arg.equals(MAP.fStr)) {
        res = MAP;
      } 
      else if (arg.equals(CLASSPATH.fStr)) {
        res = CLASSPATH;
      } 
      else if (arg.equals(OUTPUT.fStr)) {
        res = OUTPUT;
      }
      else if (arg.equals(LIB.fStr)) {
        res = LIB;
      }
      else {
        res = UNKNOWN;
      }
      return res;
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

}
