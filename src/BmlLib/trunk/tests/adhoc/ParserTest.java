package adhoc;

import java.io.BufferedReader;
import java.io.CharArrayReader;
import java.io.IOException;

import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;
import annot.textio.CodeFragment;

public class ParserTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    BCClass bcc;
    try {
      bcc = new BCClass(Paths.path, "adhoc.Empty");
      String code = bcc.printCode();
      System.out.println(code);
      code = CodeFragment.preProcess(code);
      System.out.println("--------------------------------");
      System.out.println(code);
      CodeFragment fgm = new CodeFragment(bcc, code);
      fgm.performChanges();
      if (!fgm.isCorrect())
        System.out.println("ERROR:" + fgm.getErrMsg());
    } catch (ClassNotFoundException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (ReadAttributeException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }

  }

}
