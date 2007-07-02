package mobius.bico.implem;
import java.io.PrintStream;

/**
 * An interface to handle the different implementation
 * Bico has to generate to. Right now, List and Maps.
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface IImplemSpecifics {
  /**
   * The type of the data structure representing the list
   * of class of the program.
   * @return a representation string.
   */
  String classType();
  
  
  String classCons(String name);
  String classEnd();
  
  /**
   * What specific libraries must be loaded before the begining
   * of the declarations.
   * @return A String - most likely libraries requires
   */
  String getBeginning();
  
  String getNoFields();
  String fieldsCons(String name);
  String fieldsEnd(String name);
  String interfaceType();
  String interfaceCons(String name);
  String interfaceEnd();
  void printExtraBodyField(PrintStream out);
  String getNoMethods();
  String methodsCons(String string);
  String methodsEnd(String string);
  String instructionsType();
  String getNoInstructions();
  String instructionsEnd(String string, int pos);
  String instructionsCons(String str, int prePos, int pos);
  
  /**
   * How we must modify the standard library name to get the
   * impementation specific version.
   * @param lib the library name to modify
   * @return an implementation specific library name
   */
  String requireLib(String lib);
  String getFileName(String pathname);

}
