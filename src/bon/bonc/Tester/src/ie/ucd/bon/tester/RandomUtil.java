package ie.ucd.bon.tester;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class RandomUtil {

  
  private static final double justJoinProbability = 0.2d;
  private static final double deleteProbability = 0.5d;
  private static final double addProbability = 0.5d;
  private static final double joinFileProbability = 0.01d;
  private static final List<Double> modProbabilities = new ArrayList<Double>();
  private static final List<Modification> mods = new ArrayList<Modification>();
  private static final double modProbSum = deleteProbability + addProbability + joinFileProbability;
  
  public static final Modification deleteMod = new RemoveTextModification();
  public static final Modification addMod = new AddTextModification();
  public static final Modification appendMod = new AppendFileModification();
  
  static {
    modProbabilities.add(deleteProbability);
    mods.add(deleteMod);
    modProbabilities.add(addProbability);
    mods.add(addMod);
    modProbabilities.add(joinFileProbability);
    mods.add(appendMod);
  }
  
  private static final double anotherModProbability = 0.99;
  
  private static Random r = new Random();
  
  public static <T> T randomlyChooseFromList(List<T> items) {
    return items.get(r.nextInt(items.size()));
  }
  
  public static boolean justJoin() {
    return r.nextDouble() < justJoinProbability;
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
