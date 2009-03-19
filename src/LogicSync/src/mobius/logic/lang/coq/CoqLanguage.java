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

import mobius.logic.lang.ILanguage;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.parser.CoqLexer;
import mobius.logic.lang.coq.parser.CoqParser;

public class CoqLanguage implements ILanguage {

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
            CoqTranslator.translate(fAst, fGenerate.get(0));
            System.out.println("The Coq Language handler generated '" + fGenerate.get(0).getName() +
                               "' from '" + fInput.get(0).getName() + "' succesfully.");
          } catch (FileNotFoundException e) {
            e.printStackTrace();
          }
        break;
      default:
        System.err.println("At this moment the Coq Language cannot " +
                           "generate more than one file!\nGot: " + fGenerate + 
                           "\nDoing nothing :(");
    }
    }
  }

  @Override
  public void prepare() {
    switch (fInput.size()) {
      case 0:
        break;
      case 1:
        fAst = parseFile(fInput.get(0));
        System.out.println("The Coq Language handler parsed '" + fInput.get(0).getName() +
                           "' succesfully.");
        break;
      default:
        System.err.println("At this moment the Coq Language cannot " +
                           "treat more than one file!\nGot:" + fInput + 
                           "\nDoing nothing :(");
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
}
