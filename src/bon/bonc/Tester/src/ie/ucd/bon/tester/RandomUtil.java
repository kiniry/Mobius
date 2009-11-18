package ie.ucd.bon.tester;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class RandomUtil {

  private static final double deleteProbability = 0.5d;
  private static final double addProbability = 0.5d;
  private static final double joinFileProbability = 0.01d;
  private static final List<Double> modProbabilities = new ArrayList<Double>();
  private static final List<Modification> mods = new ArrayList<Modification>();
  private static final double modProbSum = deleteProbability + addProbability + joinFileProbability;
  
  static {
    modProbabilities.add(deleteProbability);
    mods.add(new RemoveTextModification());
    modProbabilities.add(addProbability);
    mods.add(new AddTextModification());
    modProbabilities.add(joinFileProbability);
    mods.add(new AppendFileModification());
  }
  
  private static final double anotherModProbability = 0.99;
  
  private static Random r = new Random();
  
  public static <T> T randomlyChooseFromList(List<T> items) {
    return items.get(r.nextInt(items.size()));
  }
  
  public static boolean makeAnotherMod() {
    return r.nextDouble() < anotherModProbability;
  }
  
  public static int chooseIndex(List<Double> probabilities, double sum) {
    double rand = r.nextDouble() * sum;
    for (int i=0; i < probabilities.size(); i++) {
      if (rand < probabilities.get(i)) {
        return i;
      } else {
        rand -= probabilities.get(i);
      }
    }
    
    assert false;
    return -1;
  }
  
  public static Random getRandom() {
    return r;
  }
  
  public static Modification chooseRandomModification() {
    return mods.get(chooseIndex(modProbabilities, modProbSum));
  }
  
}
