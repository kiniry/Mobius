package mobius.logic.lang.boogie;

import java.io.File;
import java.io.IOException;

import freeboogie.ast.Declaration;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;
import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import mobius.logic.lang.ABasicLanguage;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.TypeCheckedAst;

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
  @Override public void generateFrom(final TypeCheckedAst ast) {
    assert false : "todo";
  }

  /** {@inheritDoc} */
  @Override public GenericAst extractGenericAst() {
    for (File f : getInput()) {
      try {
        final FbParser parser = new FbParser(
          new CommonTokenStream(new FbLexer(
            new ANTLRFileStream(f.getAbsolutePath()))));
        parser.fileName = f.getName();
        final Declaration d = parser.program();
      } 
      catch (IOException e) {
        e.printStackTrace(); // FIXME
      } 
      catch (RecognitionException e) {
        e.printStackTrace(); // FIXME
      }
    }
    assert false : "todo";
    return null;
  }

  /** {@inheritDoc} */
  @Override public void mergeWith(final GenericAst ast) {
    assert false : "todo";
  }
  
  /** {@inheritDoc} */
  @Override
  public String getName() {
    return "Boogie";
  }
}

