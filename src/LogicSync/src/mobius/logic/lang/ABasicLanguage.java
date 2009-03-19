package mobius.logic.lang;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public abstract class ABasicLanguage extends ALanguage {
  private final List<File> fInput = new ArrayList<File>();
  private final List<File> fGenerate = new ArrayList<File>();
  private final List<File> fMerge = new ArrayList<File>();
  
  @Override
  public void addGenerate(final File gen) {
    getGenerate().add(gen);
  }

  @Override
  public void addInput(final File in) {
    getInput().add(in);
  }

  @Override
  public void addMerge(File merge) {
    getMerge().add(merge);
  }

  public List<File> getInput() {
    return fInput;
  }

  public List<File> getGenerate() {
    return fGenerate;
  }

  public List<File> getMerge() {
    return fMerge;
  }

  
}
