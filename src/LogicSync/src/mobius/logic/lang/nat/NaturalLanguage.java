package mobius.logic.lang.nat;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import mobius.logic.lang.ALanguage;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.nat.ast.NLAst;
import mobius.logic.lang.nat.ast.Program;
import mobius.logic.lang.nat.parser.NLLexer;
import mobius.logic.lang.nat.parser.NLParser;

import mobius.logic.lang.generic.ast.TypeCheckedAst;
import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

public class NaturalLanguage extends ALanguage {

  private final List<File> fInput;
  private final List<File> fGenerate;
  private final List<File> fMerge;

  private Program tree;

  public NaturalLanguage() {
    fInput = new ArrayList<File>();
    fGenerate = new ArrayList<File>();
    fMerge = new ArrayList<File>();
  }

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
  public boolean isLanguageFile(final File f) {
    return f.getName().endsWith(".lnl");
  }

  @Override
  public void generateFrom(TypeCheckedAst ast) {
    GenericToNLTranslator translator = new GenericToNLTranslator();
    NLAst translatedAst = translator.translate(ast.getAst());
    
    if (translatedAst != null) {
      if (fGenerate.size() == 1) {
        System.out.print(this + ": generating '" + fGenerate.get(0).getName() + "'...");
        try {
          NLPrettyPrinter pp = new NLPrettyPrinter(new PrintStream(new FileOutputStream(fGenerate.get(0))));
          translatedAst.eval(pp);
          pp.closeStream();
          System.out.println(" done.");  
        } catch (FileNotFoundException e) {
          System.out.println(" FAILED!");
          e.printStackTrace();
        }
        
      } else if (fGenerate.size() > 1) {
        moreThanOneFileError(fGenerate);
      }
    } else {
      System.out.println("Unable to translate to NL.");
    }
  }


  @Override
  public void prepare() {
    if (fInput.size() == 1) {
      System.out.print(this + ": parsing '" + fInput.get(0).getName() + "'...");
      tree = parseFile(fInput.get(0));
      if(tree != null) {
        System.out.println(" done.");
      }
      else {
        System.out.println(" FAILED!");
      }
    } else if (fInput.size() > 1) {
      moreThanOneFileError(fInput);
    }
  }

  public static Program parseFile(File f) {
    try {
      CharStream cs = new ANTLRFileStream(f.getAbsolutePath());
      NLLexer cl = new NLLexer(cs);
      NLParser parser = new NLParser(new CommonTokenStream(cl));
      Program ast = parser.program();
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

  @Override
  public String toString() {
    return "Natural language handler";
  }

  @Override
  public GenericAst extractGenericAst() {
    return new NLToGenericTranslator().evalProgram(tree.getLogics());
  }

  @Override
  public void mergeWith(GenericAst ast) {
    // TODO Auto-generated method stub
    
  }

  /** {@inheritDoc} */
  @Override
  public String getName() {
    return "Natural";
  }
  
}
