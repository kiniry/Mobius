/** Public domain. */
package freeboogie.ast;

/** Base class for the AST hierarchy. */
public abstract class Ast {
  abstract public <R> R eval(Evaluator<R> e);
}
