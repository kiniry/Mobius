package bico;
import java.io.BufferedWriter;
import java.io.IOException;

public interface ImplemSpecifics {

  public String classType();
  public String classCons(String name);
  public String classEnd();
  public String getBeginning();
  public String getNoFields();
  public String fieldsCons(String name);
  public String fieldsEnd(String name);
  public String interfaceType();
  public String interfaceCons(String name);
  public String interfaceEnd();
  public void printExtraBodyField(BufferedWriter out) throws IOException;
  public String getNoMethods();
  public String methodsCons(String string);
  public String methodsEnd(String string);
  public String instructionsType();
  public String getNoInstructions();
  public String instructionsEnd(String string, int pos);
  public String instructionsCons(String str, int pos_pre, int pos);
  public String requireLib(String string);
  public String getFileName(String pathname);

}
