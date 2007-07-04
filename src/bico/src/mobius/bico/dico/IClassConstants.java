package mobius.bico.dico;

/**
 * This interface contains the class constants used by
 * the dictionnary.
 * <pre>
 *   (* IMPORTANT CONSTANT CONVENTIONS FOR PARSER !! *)
 *  Definition javaLang : PackageName := 1.
 *  Definition EmptyPackageName : PackageName := 2.
 *  Definition javaIo: PackageName := 3.
 *  
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
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface IClassConstants {
  /** the number for empty packages. */
  int pkgEmpty = 1;
  /** the number for the java.lang packages. */
  int pkgJavaLang = 2;
  /** the number for the java.io package. */
  int pkgJavaIo = 3;
  
  /** the number for the Object class. */
  int object = 1;
  /** the number for the Exception class. */
  int exception = 2;
  /** the number for the RuntimeException class. */
  int runtimeException = 3;
  /** the number for the NullPointerException class. */
  int nullPointerException = 4;
  /** the number for the ArrayIndexOutOfBoundsException class. */
  int arrayIndexOutOfBoundsException = 5;
  /** the number for the ArrayStoreException class. */
  int arrayStoreException = 6;
  /** the number for the NegativeArraySizeException class. */
  int negativeArraySizeException = 7;
  /** the number for the ClassCastException class. */
  int classCastException = 8;
  /** the number for the ArithmeticException class. */
  int arithmeticException = 9;
  /** the number for the Throwable class. */
  int throwable = 10;
  /** the number for the Cloneable interface. */
  int cloneable = 11;
  /** the number for the Serializable interface. */
  int serializable = 12;
  /** the number for the String class. */
  int string = 13;
  
  /** constant for the methods: right now it is arbitrary. */
  int methThrw = 11;
  /** constant for the methods: right now it is arbitrary. */
  int methExcp = 10;
  /** constant for the methods: right now it is arbitrary. */
  int methStr = 13;
  /** constant for the methods: right now it is arbitrary. */
  int methObj = 12;
  
}
