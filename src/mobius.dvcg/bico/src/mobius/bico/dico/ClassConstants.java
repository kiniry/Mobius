package mobius.bico.dico;

/**
 * This interface contains the class constants used by
 * the dictionnary.

 * @author J. Charles (julien.charles@inria.fr)
 */
public final class ClassConstants {
  /**
   * A type representing Class constants.
   * <pre>
   *  (* IMPORTANT CONSTANT CONVENTIONS FOR PARSER !! *)
   *  Definition object : ShortClassName := 1.
   *  Definition exception : ShortClassName := 2.
   *  Definition RuntimeException : ShortClassName := 3.
   *  Definition NullPointerException : ShortClassName := 4.
   *  Definition ArrayIndexOutOfBoundsException : ShortClassName := 5.
   *  Definition ArrayStoreException : ShortClassName := 6.
   *  Definition NegativeArraySizeException : ShortClassName := 7.
   *  Definition ClassCastException : ShortClassName := 8.
   *  Definition ArithmeticException : ShortClassName := 9.
   *  Definition throwable : ShortClassName := 10.
   *  Definition cloneable: ShortClassName := 11.
   *  Definition serializable: ShortClassName := 12.
   * </pre>
   */
  public enum Clss {
    /** to get rid of the ordinal 0. */
    Nil,
    /** the number for the Object class (1). */
    object,
    /** the number for the Exception class (2). */
    exception,
    /** the number for the RuntimeException class (3). */
    runtimeException,
    /** the number for the NullPointerException class (4). */
    nullPointerException,
    /** the number for the ArrayIndexOutOfBoundsException class (5). */
    arrayIndexOutOfBoundsException,
    /** the number for the ArrayStoreException class (6). */
    arrayStoreException,
    /** the number for the NegativeArraySizeException class (7). */
    negativeArraySizeException,
    /** the number for the ClassCastException class (8). */
    classCastException,
    /** the number for the ArithmeticException class (9). */
    arithmeticException,
    /** the number for the Throwable class (10). */
    throwable,
    /** the number for the Cloneable interface (11). */
    cloneable,
    /** the number for the Serializable interface (12). */
    serializable,
    /** the number for the String class (13). */
    string;
  }
  
  
  /**
   * A type representing Package constants. 
   *  <pre>
   *  (* IMPORTANT CONSTANT CONVENTIONS FOR PARSER !! *)
   *  Definition javaLang : PackageName := 1.
   *  Definition EmptyPackageName : PackageName := 2.
   *  Definition javaIo: PackageName := 3.
   *  </pre>
   * @author J. Charles (julien.charles@inria.fr)
   */
  public enum Pkg {
    /** to get rid of the ordinal 0. */
    Nil,
    /** the number for empty packages. */
    Empty,
    /** the number for the java.lang packages. */
    JavaLang,
    /** the number for the java.io package. */
    JavaIo;
  }

  
  /**
   * A type representing methods constants. 
   * @author J. Charles (julien.charles@inria.fr)
   */
  //FIXME: why does it begins at 10 ?
  public enum Meth {
    /** Constant for the constructor method of a Throwable object. */
    Thrw("Throwable.<init>", 11),
    /** Constant for the constructor method of a Exception object. */
    Excp("Exception.<init>", 10), 
    /** Constant for the constructor method of a String object. */
    Str("String.<init>", 13), 
    /** Constant for the constructor method of a Object object. */
    Obj("Object.<init>", 12),
    /** Constant for the constructor method of a NullPointerException object. */
    NullExcp("NullPointerException.<init>", 10);
    
    /** a number associated with a constant. */
    private final int fNum;
    /** the name associated with the string. */
    private final String fStr;  
    /**
     * Construct an object. 
     * @param i the number associated with the constant
     * @param str the string associated with the constant
     */
    private Meth(final String str, final int i) {
      fNum = i;
      fStr = str;
    }

    /**
     * @return the number associated with the constant
     */
    public int toInt() {
      return fNum;
    }
    /** {@inheritDoc} */
    public String toString() {
      return fStr;
    }
  }
  
}
