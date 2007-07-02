package mobius.bico.implem;
import java.io.PrintStream;


public class ListImplemSpecif implements IImplemSpecifics {

  public String classType() {
    return "list Class";
  }
  public String interfaceCons(final String name) {
    return name + " :: ";
  }
  public String interfaceEnd() {
    return "nil";
  }
  public String classCons(final String name) {
    return name + " :: ";
  }
  public String classEnd() {
    return "nil";
  }
  public String getBeginning() {
    return "Require Import ImplemProgramWithList.";
  }
  public String getNoFields() {
    return "nil";
  }
  public String fieldsCons(final String name) {
    return name + " :: ";
  }
  public String fieldsEnd(final String name) {
    return name + " :: nil";
  }

  public String getNoMethods() {
    return "nil";
  }
  public String methodsCons(final String name) {
    return name + " :: ";
  }
  public String methodsEnd(final String name) {
    return name + " :: nil";
  }
  public String interfaceType() {
    return "list Interface";
  }
  public String interfaceEmpty() {
    return "nil";
  }
  public void printExtraBodyField(final PrintStream out) {

  }
  public String instructionsType() {
    return "list (PC*Instruction)";
  }
  public String getNoInstructions() {
    return "nil";
  }
  public String instructionsCons(final String name, final int pos, 
                                 final int pos_next) {
    return "(" + pos + "%N, " + name + ") :: ";
  }
  public String instructionsEnd(final String name, final int pos) {
    return  "(" + pos + "%N, " + name + ") :: nil";
  }
  public String requireLib(final String string) {
    return "List_" + string;
  }
  public String getFileName(final String pathname) {
    return pathname + "List";
  }
  public String toString() {
    return "List implementation";
  }
}
