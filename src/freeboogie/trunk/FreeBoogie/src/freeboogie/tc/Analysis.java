package freeboogie.tc;

import java.util.List;
import freeboogie.ast.Ast;

/**
 * An {@ Analyzer} is an object that can produce a list of
 * errors for a given AST.
 */
interface Analyzer {
  List<Error> analyze(Ast ast);
}
