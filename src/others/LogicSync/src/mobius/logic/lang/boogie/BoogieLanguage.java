package mobius.logic.lang.boogie;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import freeboogie.ast.Declaration;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;
import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import mobius.logic.lang.ABasicLanguage;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.TypeCheckedAst;
import mobius.util.Logger;

/** 
 * Support for Boogie. 
 *
 * @author rgrig@
 */
public class BoogieLanguage extends ABasicLanguage {
  private BoogieOfGeneric boogie;
  private GenericOfBoogie generic;

  /** {@inheritDoc} */
  @Override public boolean isLanguageFile(final File f) {
    return f.getName().endsWith(".bpl");
  }

  /** Initialize. */
  @Override public void prepare() {
    boogie = new BoogieOfGeneric();
    generic = new GenericOfBoogie();
  }

  /** {@inheritDoc} */
  @Override public void generateFrom(final TypeCheckedAst ast) {
    System.out.println("  Generate Boogie.");
    Declaration boogieAst = boogie.getFrom(ast);
    for (File f : getGenerate()) {
      try {
        FileWriter w = new FileWriter(f);
        PrettyPrinter pp = new PrettyPrinter(w);
        boogieAst.eval(pp);
        w.close();
      } 
      catch (IOException e) {
        Logger.warn.println("  Can't write to " + f.getName());
        e.printStackTrace();
      }
    }
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
        return generic.getFrom(d);
      } 
      catch (IOException e) {
        e.printStackTrace(); // FIXME
      } 
      catch (RecognitionException e) {
        e.printStackTrace(); // FIXME
      }
    }
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

