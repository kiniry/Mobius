package mobius.bico.implem;
import java.io.PrintStream;

/**
 * This class handles elements specific to the map implementation.
 * It uses the Map data structure from the formalisation library.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class MapImplemSpecif implements IImplemSpecifics {
  
  /** closing parenthese for interfaces enumeration. */
  private String fInterfaceParen = "";
  
  /** closing parenthese for instructions enumeration. */
  private String fInstrParen = "";
  
  /** closing parenthese for classes enumeration. */
  private String fClassParen = "";
  
  /** closing parenthese for fields enumeration. */
  private String fFieldsParen = "";
  
  /** closing parenthese for methods enumeration. */
  private String fMethodsParen = "";
  
  /**
   * @see IImplemSpecifics#classType()
   * @return <code>PROG.MapClass.t</code>
   */
  public String classType() {
    return "PROG.MapClass.t";
  }
  
  /**
   * @see IImplemSpecifics#interfaceType()
   * @return <code>PROG.MapInterface.t</code>
   */
  public String interfaceType() {
    return "PROG.MapInterface.t";
  }
  
  /**
   * @see IImplemSpecifics#interfaceCons(java.lang.String)
   * @param name the name of the interface
   * @return <code>(mi_cons name </code>
   */
  public String interfaceCons(final String name) {
    fInterfaceParen += ")";
    return "(mi_cons " + name;
  }
  
  /**
   * @see IImplemSpecifics#interfaceEnd()
   * @return <code>mi_empty)))...)</code> (several parenthese)
   */
  public String interfaceEnd() {
    final String res = "mi_empty" + fInterfaceParen;
    fInterfaceParen = "";
    return res;
  }
  
  
  /**
   * @see IImplemSpecifics#classCons(java.lang.String)
   * @param name the name of the class
   * @return <code>(mc_cons name </code>
   */
  public String classCons(final String name) {
    fClassParen += ")";
    return "(mc_cons " + name;
  }
  
  /**
   * @see IImplemSpecifics#classEnd()
   * @return <code>mc_empty)))...)</code> (several parenthese)
   */
  public String classEnd() {
    final String res = "mc_empty" + fClassParen;
    fClassParen = "";
    return res;
  }
  
  /**
   * @see IImplemSpecifics#getBeginning()
   * @return <code>Require Import ImplemProgramWithMap.</code>
   */
  public String getBeginning() {
    return "Require Export ImplemProgramWithMap.";
  }

  /**
   * @see IImplemSpecifics#getNoFields()
   * @return <code>mf_empty</code>
   */
  public String getNoFields() {
    return "mf_empty";
  }

  /**
   * @see IImplemSpecifics#fieldsCons(java.lang.String)
   * @param name the name of the field
   * @return <code>(mf_cons name </code>
   */
  public String fieldsCons(final String name) {
    fFieldsParen += ")";
    return "(mf_cons " + name;
  }
  
  /**
   * @see IImplemSpecifics#fieldsEnd(java.lang.String)
   * @param name the name of the field
   * @return <code>(mf_single name))))...)</code> (several parenthese)
   */
  public String fieldsEnd(final String name) {
    final String res = "(mf_single " + name + ")" + fFieldsParen;
    fFieldsParen = "";
    return res;
  }

  /**
   * @see IImplemSpecifics#getNoMethods()
   * @return <code>ms_empty</code>
   */
  public String getNoMethods() {
    return "ms_empty";
  }

  /**
   * @see IImplemSpecifics#methodsCons(java.lang.String)
   * @param name the name of the method
   * @return <code>(ms_cons name</code>
   */
  public String methodsCons(final String name) {
    fMethodsParen += ")";
    return "(ms_cons " + name;
  }
  
  /**
   * @see IImplemSpecifics#methodsEnd(java.lang.String)
   * @param name the name of the method
   * @return <code>(ms_single name))))...)</code> (several parenthese)
   */
  public String methodsEnd(final String name) {
    final String res = "(ms_single " + name + ")" + fMethodsParen;
    fMethodsParen = "";
    return res;
  }
  
  /**
   * Prints the point of the first instruction of the methods;
   * the so-called entry-point.
   * @param out a valid stream
   * @see IImplemSpecifics#printExtraBodyField(PrintStream)
   */
  public void printExtraBodyField(final PrintStream out) {
    out.println("0%N");
  }
  
  
  /**
   * @see IImplemSpecifics#instructionsType()
   * @return <code>MapN.t (Instruction*option PC)</code>
   */
  public String instructionsType() {
    return "MapN.t (Instruction*option PC)";
  }

  /**
   * @see IImplemSpecifics#getNoInstructions()
   * @return <code>bc_single 0%N Return</code>
   */
  public String getNoInstructions() {
    return "bc_single 0%N Return";
  }

  /**
   * @see IImplemSpecifics#instructionsCons(String, int, int)
   * @param name the name of the instruction
   * @param pos the position of the instruction which is treated
   * @param nextPos the position of the next instruction
   * @return <code>(bc_cons pos%N name nextPos%N</code>
   */
  public String instructionsCons(final String name, final int pos, 
                                 final int nextPos) {
    fInstrParen += ")";
    return "(bc_cons " + pos + "%N " + name + " " + nextPos + "%N ";
  }
  
  /**
   * @see IImplemSpecifics#instructionsEnd(String, int)
   * @param name the name of the instruction
   * @param pos the position of the instruction which is treated
   * @return <code>(bc_single pos%N name nextPos%N))))...)</code>
   * (several parenthese)
   */
  public String instructionsEnd(final String name, final int pos) {
    final String res = "(bc_single " + pos + "%N " + name + ")" + fInstrParen;
    fInstrParen = "";
    return res;
  }
  
  /**
   * @see IImplemSpecifics#requireLib(String)
   * @param lib the lib name to make implementation specific
   * @return <code>Map_lib</code>
   */
  public String requireLib(final String lib) {
    return "Map_" + lib;
  }
  
  /**
   * @see IImplemSpecifics#getFileName(String)
   * @param pathname the path name to make implementation specific
   * @return <code>pathnameMap</code>
   */
  public String getFileName(final String pathname) {
    return pathname + "Map";
  }
  
  /**
   * Returns a string that tells which implementation is
   * used.
   * @return <code>Map Implementation</code>
   */
  public String toString() {
    return "Map implementation";
  }
}
