package mobius.bico.implem;
import java.io.BufferedWriter;
import java.io.PrintStream;


public class ListImplemSpecif implements IImplemSpecifics {

  public String classType() {
    return "list Class";
  }
  public String interfaceCons(String name) {
    return name + " :: ";
  }
  public String interfaceEnd() {
    return "nil";
  }
  public String classCons(String name) {
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
  public String fieldsCons(String name) {
    return name + " :: ";
  }
  public String fieldsEnd(String name) {
    return name + " :: nil";
  }

  public String getNoMethods() {
    return "nil";
  }
  public String methodsCons(String name) {
    return name + " :: ";
  }
  public String methodsEnd(String name) {
    return name + " :: nil";
  }
  public String interfaceType() {
    return "list Interface";
  }
  public String interfaceEmpty() {
    return "nil";
  }
  public void printExtraBodyField(PrintStream out) {

  }
  public String instructionsType() {
    return "list (PC*Instruction)";
  }
  public String getNoInstructions() {
    return "nil";
  }
  public String instructionsCons(String name, int pos, int pos_next) {
    return "(" + pos + "%N, " + name + ") :: ";
  }
  public String instructionsEnd(String name, int pos) {
    return  "(" + pos + "%N, " + name + ") :: nil";
  }
  public String requireLib(String string) {
    return "Require Import List_" + string + ".";
  }
  public String getFileName(String pathname) {
    return pathname + "List";
  }
  public String toString() {
    return "List implementation";
  }
}
