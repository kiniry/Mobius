package mobius.bico;

/**
 * This class is used as a library to handle constants.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class Constants {
  /** the separator for the packages. */
  public static final char JAVA_NAME_SEPARATOR = '.';
  
  /**
   * A constant which represents a file suffix.
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static enum Suffix {
    /** the class suffix. */
    CLASS(".class"),
    /** the coq files extension (.v). */
    COQ(".v");
    /** the string representing the constant. */
    private final String fStr;
    /**
     * Construct a Suffix out of its representation.
     * @param s the string representation
     */
    private Suffix(final String s) {
      fStr = s;
    }
    /** {@inheritDoc} */
    public String toString() {
      return fStr;
    }
    
    /**
     * @return the length of the string constant
     */
    public int length() {
      return fStr.length();
    }
  }
  
  /**
   * Constants representing options passed to  
   * the entry point.
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static enum Option {
    /** To have the map implementation. */
    MAP("-map"),
    /** To have the list implementation. */
    LIST("-list"),
    /** The base working class path. */
    CLASSPATH("-cp"),
    /** The output directory. */
    OUTPUT("-o"),
    /** To show the help message. */
    HELP("-help"),
    /** 
     * Enables the java.lang library generation. 
     * It implies the generation of most of the JRE. 
     */
    LIB("-lib"), 
    /** The option if all else fails. */
    UNKNOWN(""); 
    
    /** The string representing the option. */
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
      final String low = arg.toLowerCase();
      Option res = UNKNOWN;
      
      if (low.equals(HELP.fStr)) {
        res = HELP;
      } 
      else if (low.equals(LIST.fStr)) {
        res = LIST;
      } 
      else if (low.equals(MAP.fStr)) {
        res = MAP;
      } 
      else if (low.equals(CLASSPATH.fStr)) {
        res = CLASSPATH;
      } 
      else if (low.equals(OUTPUT.fStr)) {
        res = OUTPUT;
      }
      else if (low.equals(LIB.fStr)) {
        res = LIB;
      }
      else {
        res = UNKNOWN;
      }
      return res;
    }

    /**
     * If it is an option made out of two arguments.
     * @return answers yes uf the option has a second argument
     */
    public boolean is2ArgsOption() {
      switch (this) {
        case CLASSPATH:
        case OUTPUT:
          return true;
        default:
          break;
      }
      return false;
    }
  }

 

}
