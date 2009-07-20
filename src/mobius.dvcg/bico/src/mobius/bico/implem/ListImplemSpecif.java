package mobius.bico.implem;
import java.io.PrintStream;

/**
 * This class handles elements specific to the list implementation.
 * Basically it tells how to do nice <code>cons</code>, 
 * put <code>nil</code> where your mouth is etc.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ListImplemSpecif implements IImplemSpecifics {
  
  /**
   * Returns a string that tells which implementation is
   * used.
   * @return <code>List Implementation</code>
   */
  public String toString() {
    return "List implementation";
  }
  
  /**
   * @see IImplemSpecifics#getBeginning()
   * @return <code>Require Import ImplemProgramWithList.</code>
   */
  public String getBeginning() {
    return "Require Export ImplemProgramWithList.";
  }
  
  /**
   * @see IImplemSpecifics#requireLib(String)
   * @param lib the lib name to make implementation specific
   * @return <code>List_lib</code>
   */
  public String requireLib(final String lib) {
    return "List_" + lib;
  }
  
  /**
   * @see IImplemSpecifics#getFileName(String)
   * @param pathname the path name to make implementation specific
   * @return <code>pathnameList</code>
   */
  public String getFileName(final String pathname) {
    return pathname + "List";
  }

  
  /**
   * @see IImplemSpecifics#classType()
   * @return <code>list Class</code>
   */
  public String classType() {
    return "list Class";
  }
  

  
  /**
   * @see IImplemSpecifics#classCons(java.lang.String)
   * @param name the name of the class
   * @return <code>name ::</code>
   */
  public String classCons(final String name) {
    return name + " :: ";
  }
  
  /**
   * @see IImplemSpecifics#classEnd()
   * @return <code>nil</code>
   */
  public String classEnd() {
    return "nil";
  }
  

  /**
   * @see IImplemSpecifics#interfaceType()
   * @return <code>list Interface</code>
   */
  public String interfaceType() {
    return "list Interface";
  }

  
  /**
   * @see IImplemSpecifics#interfaceCons(java.lang.String)
   * @param name the name of the interface
   * @return <code>name ::</code>
   */
  public String interfaceCons(final String name) {
    return name + " :: ";
  } 
  
  /**
   * @see IImplemSpecifics#interfaceEnd()
   * @return <code>nil</code>
   */
  public String interfaceEnd() {
    return "nil";
  }
  
  /**
   * @see IImplemSpecifics#getNoFields()
   * @return <code>nil</code>
   */
  public String getNoFields() {
    return "nil";
  }
  
  /**
   * @see IImplemSpecifics#fieldsCons(java.lang.String)
   * @param name the name of the field
   * @return <code>name ::</code>
   */
  public String fieldsCons(final String name) {
    return name + " :: ";
  }
  
  /**
   * @see IImplemSpecifics#fieldsEnd(java.lang.String)
   * @param name the name of the field
   * @return <code>name :: nil</code>
   */
  public String fieldsEnd(final String name) {
    return name + " :: nil";
  }

  /**
   * @see IImplemSpecifics#getNoMethods()
   * @return <code>nil</code>
   */
  public String getNoMethods() {
    return "nil";
  }
  
  /**
   * @see IImplemSpecifics#methodsCons(java.lang.String)
   * @param name the name of the method
   * @return <code>name ::</code>
   */
  public String methodsCons(final String name) {
    return name + " :: ";
  }
  
  /**
   * @see IImplemSpecifics#methodsEnd(java.lang.String)
   * @param name the name of the method
   * @return <code>name :: nil</code>
   */
  public String methodsEnd(final String name) {
    return name + " :: nil";
  }
  
  
  /**
   * Prints nothing.
   * @param out ignored
   */
  public void printExtraBodyField(final PrintStream out) {
  }
  
  /**
   * @see IImplemSpecifics#instructionsType()
   * @return <code>list (PC*Instruction)</code>
   */
  public String instructionsType() {
    return "list (PC*Instruction)";
  }
  
  /**
   * @see IImplemSpecifics#getNoInstructions()
   * @return <code>nil</code>
   */
  public String getNoInstructions() {
    return "nil";
  }
  
  /**
   * @see IImplemSpecifics#instructionsCons(String, int, int)
   * @param name the name of the instruction
   * @param pos the position of the instruction which is treated
   * @param nextPos ignored
   * @return <code>(pos%N, name) ::</code>
   */
  public String instructionsCons(final String name, final int pos, 
                                 final int nextPos) {
    return "(" + pos + "%N, " + name + ") :: ";
  }
  
  /**
   * @see IImplemSpecifics#instructionsEnd(String, int)
   * @param name the name of the instruction
   * @param pos the position of the instruction which is treated
   * @return <code>(pos%N, name) ::nil</code>
   */
  public String instructionsEnd(final String name, final int pos) {
    return  "(" + pos + "%N, " + name + ") :: nil";
  }

}
