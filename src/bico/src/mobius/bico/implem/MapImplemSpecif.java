package mobius.bico.implem;
import java.io.PrintStream;

import mobius.bico.Util;

public class MapImplemSpecif implements IImplemSpecifics {
  String interfaceParen = "";
  String instructionsParen = "";
  String classParen = "";
  String fieldsParen = "";
  String methodsParen = "";
  
  public String classType() {
    return "PROG.MapClass.t";
  }
  public String interfaceType() {
    return "PROG.MapInterface.t";
  }

  public String interfaceCons(final String name) {
    interfaceParen += ")";
    return "(mi_cons " + name;
  }
  public String interfaceEnd() {
    final String res = "mi_empty" + interfaceParen;
    interfaceParen = "";
    return res;
  }
  public String interfaceEmpty() {
    return "mi_empty";
  }

  public String classCons(final String name) {
    classParen += ")";
    return "(mc_cons " + name;
  }
  public String classEnd() {
    final String res = "mc_empty" + classParen;
    classParen = "";
    return res;
  }
  public String getBeginning() {
    return "Require Import ImplemProgramWithMap.";
  }

  public String getNoFields() {
    return "mf_empty";
  }


  public String fieldsCons(final String name) {
    fieldsParen += ")";
    return "(mf_cons " + name;
  }
  public String fieldsEnd(final String name) {
    final String res = "(mf_single " + name + ")" + fieldsParen;
    fieldsParen = "";
    return res;
  }

  public String getNoMethods() {
    return "ms_empty";
  }


  public String methodsCons(final String name) {
    methodsParen += ")";
    return "(ms_cons " + name;
  }
  public String methodsEnd(final String name) {
    final String res = "(ms_single " + name + ")" + methodsParen;
    methodsParen = "";
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
                                 final int pos_next) {
    instructionsParen += ")";
    return "(bc_cons " + pos + "%N " + name + " " + pos_next + "%N ";
  }
  public String instructionsEnd(final String name, final int pos) {
    final String res = "(bc_single " + pos + "%N " + name + ")" + instructionsParen;
    instructionsParen = "";
    return res;
  }
  public String requireLib(final String string) {
    return "Require Import Map_" + string + ".";
  }
  public String getFileName(final String pathname) {
    return pathname + "Map";
  }
  
  public String toString() {
    return "Map implementation";
  }
}
