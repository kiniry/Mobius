package mobius.logic.lang.boogie;

import java.io.File;

import mobius.logic.lang.ABasicLanguage;
import mobius.logic.lang.generic.ast.GenericAst;

/** 
 * Support for Boogie. 
 *
 * @author rgrig@
 */
public class BoogieLanguage extends ABasicLanguage {
  /** {@inheritDoc} */
  @Override public boolean isLanguageFile(final File f) {
    return f.getName().endsWith(".bpl");
  }

  /** Does nothing. */
  @Override public void prepare() { }

  /** {@inheritDoc} */
  @Override public void generateFrom(final GenericAst ast) {
   assert false : "todo";
  }

  /** {@inheritDoc} */
  @Override public GenericAst extractGenericAst() {
    assert false : "todo";
    return null;
  }

  /** {@inheritDoc} */
  @Override public void mergeWith(final GenericAst ast) {
    assert false : "todo";
  }
}

