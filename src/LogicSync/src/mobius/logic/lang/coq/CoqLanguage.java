package mobius.logic.lang.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import mobius.logic.lang.ABasicLanguage;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.parser.CoqLexer;
import mobius.logic.lang.coq.parser.CoqParser;
import mobius.logic.lang.generic.ast.GenericAst;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

public class CoqLanguage extends ABasicLanguage {

  private CoqAst fAst;
 
  @Override
  public boolean isLanguageFile(final File f) {
    return f.getName().endsWith(".v");
  }

  
  //FIXME
  @Override
  public void generateFrom(final GenericAst ast) {
    if (fAst != null) {
      switch (getGenerate().size()) {
        case 0:
          break;
        case 1: 
          try {
            System.out.print(this + ": generating '" + 
                             getGenerate().get(0).getName() + "'...");
            CoqTranslator.translate(fAst, getGenerate().get(0));
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
  }

  @Override
  public void prepare() {
    switch (getInput().size()) {
      case 0:
        break;
      case 1:
        System.out.print(this + ": parsing '" + getInput().get(0).getName() + "'...");
        fAst = parseFile(getInput().get(0));
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

  @Override
  public GenericAst extractGenericAst() {
    System.out.print(this + ": Extracting generic AST...");
    GenericAst ast;
    ast = ExtractGeneric.translate(fAst);
    System.out.println(" done.");
    return ast;
    
  }


  @Override
  public void mergeWith(GenericAst ast) {
    // TODO Auto-generated method stub
    
  }
}
