package mobius.logic.lang.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import mobius.logic.lang.ALanguage;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.parser.CoqLexer;
import mobius.logic.lang.coq.parser.CoqParser;

public class CoqLanguage extends ALanguage {

  private final List<File> fInput = new ArrayList<File>();
  private final List<File> fGenerate = new ArrayList<File>();
  private final List<File> fMerge = new ArrayList<File>();
  private CoqAst fAst;
  
  @Override
  public void addGenerate(File gen) {
    fGenerate.add(gen);
  }

  @Override
  public void addInput(File in) {
    fInput.add(in);
  }

  @Override
  public void addMerge(File merge) {
    fMerge.add(merge);
  }

  @Override
  public boolean isLanguageFile(File f) {
    return f.getName().endsWith(".v");
  }

  @Override
  public void generate() {
    if (fAst != null) {
      switch (fGenerate.size()) {
      case 0:
        break;
      case 1: 
        try {
            System.out.print(this + ": generating '" + fGenerate.get(0).getName() + "'...");
            CoqTranslator.translate(fAst, fGenerate.get(0));
            System.out.println(" done.");
          } catch (FileNotFoundException e) {
            System.out.println(" FAILED!");
            e.printStackTrace();
            
          }
        break;
      default:
        moreThanOneFileError(fGenerate);
    }
    }
  }

  @Override
  public void prepare() {
    switch (fInput.size()) {
      case 0:
        break;
      case 1:
        System.out.print(this + ": parsing '" + fInput.get(0).getName() + "'...");
        fAst = parseFile(fInput.get(0));
        if(fAst != null) {
          System.out.println(" done.");
        }
        else {
          System.out.println(" FAILED!");
        }
        break;
      default:
          moreThanOneFileError(fInput);
    }
  }

  public static CoqAst parseFile(File f) {
    
    try {
      CharStream cs = new ANTLRFileStream(f.getAbsolutePath());
      CoqLexer cl = new CoqLexer(cs);
      CoqParser parser = new CoqParser(new CommonTokenStream(cl));
      CoqAst ast = parser.prog();
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

  public String toString() {
    return "Coq language handler";
  }
}
