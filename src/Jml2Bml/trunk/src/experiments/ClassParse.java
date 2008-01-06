package experiments;

import java.io.IOException;

import org.apache.bcel.generic.InstructionList;

public class ClassParse {

  public static void main(String[] args) throws IOException,
      ClassNotFoundException, ReadAttributeException {
    BCClass cls = new BCClass(ProjectDirectory.PROJECT_DIR + "\\classes",
                              "toCompile.TestClass");
    for (int i = 0; i < cls.getMethodCount(); i++) {
      BCMethod method = cls.getMethod(i);
      System.out.println(method);
      InstructionList il = method.getInstructions();
      System.out.println("eLLo");
    }
  }
}
