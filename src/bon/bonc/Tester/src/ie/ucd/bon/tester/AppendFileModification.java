package ie.ucd.bon.tester;

import java.io.File;
import java.util.List;

public class AppendFileModification implements Modification {

  @Override
  public void modify(StringBuilder string, List<Pair<File, String>> otherInputs) {
//    System.out.println("Append mod");
    Pair<File, String> chosen = RandomUtil.randomlyChooseFromList(otherInputs);
    string.append(chosen.getSecond());
  }

}
