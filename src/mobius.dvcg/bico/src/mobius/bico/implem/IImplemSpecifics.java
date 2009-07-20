package mobius.bico.implem;
import java.io.PrintStream;

/**
 * An interface to handle the different implementation
 * Bico has to generate to. Right now, List and Maps.
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface IImplemSpecifics {
  /**
   * How we must modify the standard library name to get the
   * impementation specific version.
   * @param lib the library name to modify
   * @return an implementation specific library name
   */
  String requireLib(String lib);
  
  /**
   * Turn a file name into an implementation specific name. 
   * @param pathname the path name to make implementation specific
   * @return an implem specific pathname
   */
  String getFileName(String pathname);
  
  /**
   * What specific libraries must be loaded before the begining
   * of the declarations.
   * @return A String - most likely libraries requires
   */
  String getBeginning();
  
  
  /**
   * The type of the data structure representing the list
   * of class of the program.
   * @return a representation string.
   */
  String classType();
  
  /**
   * Returns the equivalent of a cons for the list of class.
   * The tail argument is not mentionned.
   * @param name the first argument of the cons  
   * @return (cons name 
   */
  String classCons(String name);
  
  /**
   * The tail representing the end of the list.
   * @return usually nil
   */
  String classEnd();
  
  /**
   * The type of the data structure representing the list
   * of interface of the program.
   * @return a representation string.
   */
  String interfaceType();
  
  /**
   * Returns the equivalent of a cons for the list of interface.
   * The tail argument is not mentionned.
   * @param name the first argument of the cons  
   * @return (cons name 
   */
  String interfaceCons(String name);
  /**
   * The tail representing the end of the list.
   * @return usually nil
   */
  String interfaceEnd();
  
  /**
   * The tail representing the list if it is empty.
   * @return usually nil
   */
  String getNoFields();
  
  /**
   * Returns the equivalent of a cons for the list of fields.
   * The tail argument is not mentionned.
   * @param name the first argument of the cons  
   * @return (cons name 
   */
  String fieldsCons(String name);
  /**
   * The tail representing the end of the list.
   *  @param name the first argument of the cons  
   * @return (cons name nil)
   */
  String fieldsEnd(String name);
  

  /**
   * The tail representing the list if it is empty.
   * @return usually nil
   */
  String getNoMethods();
  
  /**
   * Returns the equivalent of a cons for the list of methods.
   * The tail argument is not mentionned.
   * @param name the first argument of the cons  
   * @return (cons name 
   */
  String methodsCons(String name);
  
  /**
   * The tail representing the end of the list.
   *  @param name the first argument of the cons  
   * @return (cons name nil)
   */
  String methodsEnd(String name);
  
  
  /**
   * Print an extra field to represents body
   * (necessary for the map implementation).
   * @param out the output stream to use
   */
  void printExtraBodyField(PrintStream out);
  
  /**
   * The type of the data structure representing the list
   * of instructions of a specific method.
   * @return a representation string.
   */
  String instructionsType();
  
  /**
   * The tail representing the list if it is empty.
   * @return usually nil
   */
  String getNoInstructions();
  
  /**
   * The tail representing the end of the list of instruction.
   * @param name the first argument of the cons
   * @param pos the position of the instruction  
   * @return (cons  (name, pos)  nil)
   */
  String instructionsEnd(String name, int pos);
  /**
   * Returns the equivalent of a cons for the list of methods.
   * The tail argument is not mentionned.
   * @param name the first argument of the cons  
   * @param pos the position of the instruction 
   * @param nextPos the position of the next instruction 
   * @return (cons (name, pos, nextPost) 
   */
  String instructionsCons(String name, int pos, int nextPos);
  


}
