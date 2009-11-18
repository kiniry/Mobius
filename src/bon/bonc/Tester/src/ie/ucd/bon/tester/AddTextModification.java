package ie.ucd.bon.tester;

import java.io.File;
import java.util.List;
import java.util.Random;

public class AddTextModification implements Modification {

  @Override
  public void modify(StringBuilder string, List<Pair<File, String>> otherInputs) {
//    System.out.println("Add mod");
    Pair<File, String> chosen = RandomUtil.randomlyChooseFromList(otherInputs);
    Random r = RandomUtil.getRandom();
    String text = chosen.getSecond();
    int firstIndex = r.nextInt(text.length());
    int secondIndex = firstIndex + r.nextInt(text.length()-firstIndex);
    String substring = chosen.getSecond().substring(firstIndex, secondIndex);
    int insertIndex = r.nextInt(string.length());
    string.insert(insertIndex, substring);
  }

}
