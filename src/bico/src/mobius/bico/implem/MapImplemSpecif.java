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
  
  public String classType() {
    return "PROG.MapClass.t";
  }
  
  public String interfaceType() {
    return "PROG.MapInterface.t";
  }

  public String interfaceCons(final String name) {
    fInterfaceParen += ")";
    return "(mi_cons " + name;
  }
  public String interfaceEnd() {
    final String res = "mi_empty" + fInterfaceParen;
    fInterfaceParen = "";
    return res;
  }
  public String interfaceEmpty() {
    return "mi_empty";
  }

  public String classCons(final String name) {
    fClassParen += ")";
    return "(mc_cons " + name;
  }
  public String classEnd() {
    final String res = "mc_empty" + fClassParen;
    fClassParen = "";
    return res;
  }
  public String getBeginning() {
    return "Require Import ImplemProgramWithMap.";
  }

  public String getNoFields() {
    return "mf_empty";
  }


  public String fieldsCons(final String name) {
    fFieldsParen += ")";
    return "(mf_cons " + name;
  }
  public String fieldsEnd(final String name) {
    final String res = "(mf_single " + name + ")" + fFieldsParen;
    fFieldsParen = "";
    return res;
  }

  public String getNoMethods() {
    return "ms_empty";
  }


  public String methodsCons(final String name) {
    fMethodsParen += ")";
    return "(ms_cons " + name;
  }
  public String methodsEnd(final String name) {
    final String res = "(ms_single " + name + ")" + fMethodsParen;
    fMethodsParen = "";
    return res;
  }
  public void printExtraBodyField(final PrintStream out) {
    out.println("0%N");
  }
  
  public String instructionsType() {
    return " MapN.t (Instruction*option PC)";
  }

  public String getNoInstructions() {
    return "bc_single 0%N Return";
  }


  public String instructionsCons(final String name, final int pos, 
                                 final int nextPos) {
    fInstrParen += ")";
    return "(bc_cons " + pos + "%N " + name + " " + nextPos + "%N ";
  }
  
  public String instructionsEnd(final String name, final int pos) {
    final String res = "(bc_single " + pos + "%N " + name + ")" + fInstrParen;
    fInstrParen = "";
    return res;
  }
  
  public String requireLib(final String string) {
    return "Map_" + string;
  }
  
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
