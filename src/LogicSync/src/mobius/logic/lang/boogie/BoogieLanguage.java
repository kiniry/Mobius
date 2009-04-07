package mobius.logic.lang.boogie;

import java.io.File;
import java.util.List;

import mobius.logic.lang.ALanguage;
import mobius.logic.lang.generic.ast.GenericAst;

/** 
 * Support for Boogie. 
 *
 * @author rgrig@
 */
public class BoogieLanguage extends ALanguage {
  @Override public boolean isLanguageFile(File f) {
    assert false : "todo";
    return false;
  }

  @Override public void addInput(File in) {
    assert false : "todo";
  }

  @Override public void addMerge(File merge) {
    assert false : "todo";
  }

  @Override public void addGenerate(File gen) {
    assert false : "todo";
  }

  @Override public void prepare() {
    assert false : "todo";
  }

  @Override public void generateFrom(GenericAst ast) {
    assert false : "todo";
  }

  @Override public void mergeWith(GenericAst ast) {
    assert false : "todo";
  }

  @Override public GenericAst extractGenericAst() {
    assert false : "todo";
    return null;
  }
}

