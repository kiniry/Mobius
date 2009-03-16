package mobius.logic.lang.coq;

import java.io.IOException;

import mobius.logic.lang.coq.parser.CoqLexer;
import mobius.logic.lang.coq.parser.CoqParser;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

public class Main {
  public static void main(String [] args) throws IOException, RecognitionException {
    CharStream cs = new ANTLRFileStream(args[0]);
    CoqLexer cl = new CoqLexer(cs);
    CoqParser parser = new CoqParser(new CommonTokenStream(cl));
    parser.prog();
  }
}
