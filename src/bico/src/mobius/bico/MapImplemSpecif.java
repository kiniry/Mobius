package mobius.bico;
import java.io.IOException;
import java.io.PrintStream;

public class MapImplemSpecif implements ImplemSpecifics {

  public String classType() {
    return "PROG.MapClass.t";
  }
  public String interfaceType() {
    return "PROG.MapInterface.t";
  }
  String interfaceParen = "";
  public String interfaceCons(String name) {
    interfaceParen += ")";
    return "(mi_cons " + name;
  }
  public String interfaceEnd() {
    String res = "mi_empty"+ interfaceParen;
    interfaceParen = "";
    return res;
  }
  public String interfaceEmpty() {
    return "mi_empty";
  }
  String classParen = "";
  public String classCons(String name) {
    classParen += ")";
    return "(mc_cons " + name;
  }
  public String classEnd() {
    String res = "mc_empty"+ classParen;
    classParen = "";
    return res;
  }
  public String getBeginning() {
    return "Require Import ImplemProgramWithMap.";
  }

  public String getNoFields() {
    return "mf_empty";
  }

  String fieldsParen = "";
  public String fieldsCons(String name) {
    fieldsParen += ")";
    return "(mf_cons " + name;
  }
  public String fieldsEnd(String name) {
    String res = "(mf_single "+ name + ")" + fieldsParen;
    fieldsParen = "";
    return res;
  }

  public String getNoMethods() {
    return "ms_empty";
  }

  String methodsParen = "";
  public String methodsCons(String name) {
    methodsParen += ")";
    return "(ms_cons " + name;
  }
  public String methodsEnd(String name) {
    String res = "(ms_single "+ name + ")" + methodsParen;
    methodsParen = "";
    return res;
  }
  public void printExtraBodyField(PrintStream out) {
    Executor.writeln(out,3,"0%N");
  }
  public String instructionsType() {
    return " MapN.t (Instruction*option PC)";
  }

  public String getNoInstructions() {
    return "bc_single 0%N Return";
  }

  String instructionsParen = "";
  public String instructionsCons(String name, int pos, int pos_next) {
    instructionsParen += ")";
    return "(bc_cons " + pos + "%N " + name + " " + pos_next + "%N ";
  }
  public String instructionsEnd(String name, int pos) {
    String res = "(bc_single " + pos + "%N " + name + ")" + instructionsParen;
    instructionsParen = "";
    return res;
  }
  public String requireLib(String string) {
    return "Require Import Map_" + string + ".";
  }
  public String getFileName(String pathname) {
    return pathname + "Map";
  }
}
