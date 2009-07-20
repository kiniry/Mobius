package mobius.logic.lang.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

import mobius.logic.lang.ABasicLanguage;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.parser.CoqLexer;
import mobius.logic.lang.coq.parser.CoqParser;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.TypeCheckedAst;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

public class CoqLanguage extends ABasicLanguage {

  /** the ast extracted from the input file. */
  private CoqAst fAst;

  /**
   * Test if the file finishes with '.v'.
   * @param f the file to test
   * @return true if the extension is '.v'
   */
  @Override
  public boolean isLanguageFile(final File f) {
    return f.getName().endsWith(".v");
  }

  /** {@inheritDoc} */
  @Override
  public void generateFrom(final TypeCheckedAst ast) {
    switch (getGenerate().size()) {
      case 0:
        break;
      case 1: 
        try {
          final File out = getGenerate().get(0);
          System.out.print(this + ": generating '" + 
                           out.getName() + "'...");
          final CoqAst res = ExtractToCoq.extract(ast.getAst());
          CoqTranslator.translate(res, out);
          System.out.println(" done.");
        } 
        catch (FileNotFoundException e) {
          System.out.println(" FAILED!");
          e.printStackTrace();
            
        }
        break;
      default:
        moreThanOneFileError(getGenerate());
    }
  }

  /** {@inheritDoc} */
  @Override
  public void prepare() {
    switch (getInput().size()) {
      case 0:
        break;
      case 1:
        final File in = getInput().get(0);
        System.out.print(this + ": parsing '" + in.getName() + "'...");
        fAst = parseFile(in);
        if (fAst != null) {
          System.out.println(" done.");
        }
        else {
          System.out.println(" FAILED!");
        }
        break;
      default:
        moreThanOneFileError(getInput());
    }
  }


  public static CoqAst parseFile(final File f) { 
    try {
      final CharStream cs = new ANTLRFileStream(f.getAbsolutePath());
      final CoqLexer cl = new CoqLexer(cs);
      final CoqParser parser = new CoqParser(new CommonTokenStream(cl));
      final CoqAst ast = parser.prog();
      return ast;
    }
    catch (IOException e) {
      e.printStackTrace();
    } 
    catch (RecognitionException e) {
      e.printStackTrace();
    }  
    return null;
  }

  /** @return "Coq language handler" */
  public String toString() {
    return "Coq language handler";
  }

  
  /** {@inheritDoc} */
  @Override
  public GenericAst extractGenericAst() {
    System.out.print(this + ": Extracting generic AST...");
    GenericAst ast;
    ast = ExtractGeneric.translate(fAst);
    System.out.println(" done.");
    return ast;
    
  }
  /** {@inheritDoc} */
  @Override
  public String getName() {
    return "Coq";
  }

  @Override
  public void mergeWith(GenericAst ast) {
    System.out.print(this + ": Preparing merging...");
    final File in = getMerge().get(0);
    final File out = new File(in.getParent(), in.getName() + ".merged");
    CoqAst cast = parseFile(in);
    System.out.println(" done.");

    System.out.print(this + ": Merging...");
    try {
      CoqTranslator.translate(cast, out);
      System.out.println(" done.");
    } 
    catch (FileNotFoundException e) {
      System.out.println(" FAILED.");
   
      e.printStackTrace();
    }    
  }
}
