package mobius.logic.lang.generic;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import mobius.logic.lang.ABasicLanguage;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.TypeCheckedAst;
import mobius.logic.lang.generic.parser.GenericLexer;
import mobius.logic.lang.generic.parser.GenericParser;
import mobius.util.Logger;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

public class GenericLanguage extends ABasicLanguage {
  
  @Override
  public boolean isLanguageFile(final File f) {
    return f.getName().endsWith(".fol");
  }

  @Override
  public void generateFrom(final TypeCheckedAst ast) {
    switch (getGenerate().size()) {
      case 0:
        break;
      case 1: 
        Logger.out.print(this + ": generating '" + 
                           getGenerate().get(0).getName() + "'...");
        try {
          GenericTranslator.translate(ast, getGenerate().get(0));
          Logger.out.println(" done.");
        } 
        catch (FileNotFoundException e) {
          Logger.out.println(" FAILED!");
          e.printStackTrace();
        }
   
        break;
      default:
        moreThanOneFileError(getGenerate());
    }
  }

  /** {@inheritDoc} */
  @Override
  public void prepare() { }

  
  public static GenericAst parseFile(final File f) {
    
    try {
      final CharStream cs = new ANTLRFileStream(f.getAbsolutePath());
      final GenericLexer cl = new GenericLexer(cs);
      final GenericParser parser = new GenericParser(new CommonTokenStream(cl));
      final GenericAst ast = parser.prog();
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
  
  /** @return "Generic language handler" */
  public String toString() {
    return "Generic language handler";
  }

  @Override
  public GenericAst extractGenericAst() {
    GenericAst ast = null;
    switch (getInput().size()) {
      case 0:
        break;
      case 1:
        Logger.out.print(this + ": parsing '" + getInput().get(0).getName() + "'...");
        ast = parseFile(getInput().get(0));
        if (ast != null) {
          Logger.out.println(" done.");
        }
        else {
          Logger.out.println(" FAILED!");
        }
        break;
      default:
        moreThanOneFileError(getInput());
    }
    
    return ast;
  }

  @Override
  public void mergeWith(GenericAst ast) {
    // TODO Auto-generated method stub
    
  }

  /** {@inheritDoc} */
  @Override
  public String getName() {
    return "Generic";
  }

}
