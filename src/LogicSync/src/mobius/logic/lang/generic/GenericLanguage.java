package mobius.logic.lang.generic;

import java.io.File;
import java.io.IOException;

import mobius.logic.lang.ABasicLanguage;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.parser.GenericLexer;
import mobius.logic.lang.generic.parser.GenericParser;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;

public class GenericLanguage extends ABasicLanguage {
 
  private GenericAst fAst;
  
  @Override
  public boolean isLanguageFile(final File f) {
    return f.getName().endsWith(".fol");
  }

  @Override
  public void generate() {
    if (fAst != null) {
      switch (getGenerate().size()) {
        case 0:
          break;
        case 1: 
          System.out.print(this + ": generating '" + 
                             getGenerate().get(0).getName() + "'...");
            //CoqTranslator.translate(fAst, fGenerate.get(0));
          System.out.println(" done.");
     
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

  public static GenericAst parseFile(File f) {
    
    try {
      final CharStream cs = new ANTLRFileStream(f.getAbsolutePath());
      final GenericLexer cl = new GenericLexer(cs);
      final GenericParser parser = new GenericParser(new CommonTokenStream(cl));
      //GenericAst ast = parser.prog();
      return null;
    }
    catch (IOException e) {
      e.printStackTrace();
    } 
//    catch (RecognitionException e) {
//      e.printStackTrace();
//    }  
    return null;
  }
  
  /** @return "Generic language handler" */
  public String toString() {
    return "Generic language handler";
  }

}
