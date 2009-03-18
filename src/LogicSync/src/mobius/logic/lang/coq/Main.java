package mobius.logic.lang.coq;

import java.io.File;
import java.io.IOException;

import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.parser.CoqLexer;
import mobius.logic.lang.coq.parser.CoqParser;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

public class Main {
  private static final StringEvaluator evaluator = new StringEvaluator();

  public static void main(String [] args) throws IOException, RecognitionException {
    File target = new File(args[0]);
    CoqAst ast = parseFile(target);    
    System.out.println(toStringList(ast));
    File output = new File(target.getParentFile(), "output.v");
    CoqTranslator.translate(ast, output);
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
  
  
  public static String toStringList(CoqAst ast) {
    CoqAst node = ast;
    String res = "";
    while (node != null) {
      res += ",\n " + node.eval(evaluator);
      node = node.getNext();
    }
    return "[" + res.substring(3) + "]";
  }
}
