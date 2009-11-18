package ie.ucd.bon.tester;

import java.io.File;
import java.util.List;
import java.util.Random;

public class RemoveTextModification implements Modification {

  @Override
  public void modify(StringBuilder string, List<Pair<File, String>> otherInputs) {
    //System.out.println("Rem mod");
    Random r = RandomUtil.getRandom();
    int firstIndex = r.nextInt(string.length());
    int secondIndex = firstIndex + r.nextInt(string.length()-firstIndex);
    string.delete(firstIndex, secondIndex);
  }

}
