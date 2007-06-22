package mobius.bico.implem;
import java.io.PrintStream;

public interface IImplemSpecifics {

  String classType();
  String classCons(String name);
  String classEnd();
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
  String instructionsCons(String str, int pos_pre, int pos);
  String requireLib(String string);
  String getFileName(String pathname);

}
