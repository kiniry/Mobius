package freeboogie.tc;

import java.util.*;

import genericutils.SimpleGraph;

import freeboogie.ErrorsFoundException;
import freeboogie.ast.*;

/**
 * Interface for type-checkers.
 *
 * Users call {@code process} on an AST and they get back a
 * list of type errors. Additional information can be queried
 * using the other methods. Note in particular the method {@code
 * getAST()}: It is possible for an implementation to modify the
 * AST, and in that case all the provided information referrs to
 * the modified AST.
 *
 * This behaves as a Facade for the package.
 *
 * @author rgrig
 */
public interface TcInterface {
  /**
   * Typechecks an AST.
   * @param ast the AST to check
   * @return the detected errors 
   */
  List<FbError> process(Declaration ast);

  Program process(Program p) throws ErrorsFoundException;

  /**
   * Returns the flow graph of {@code impl}.
   *  use {{@link #getFlowGraph(Body)} instead
   * @param impl the implementation whose flow graph is requested
   * @return the flow graph of {@code impl}
   */
  SimpleGraph<Block> getFlowGraph(Implementation impl);


  /**
   * Returns the flow graph of {@code bdy}.
   * @param bdy the body whose flow graph is requested
   * @return the flow graph of {@code bdy}
   */
  SimpleGraph<Block> getFlowGraph(Body bdy);
  
  /**
   * Returns the map of expressions to types.
   * @return the map of expressions to types.
   */
  Map<Expr, Type> getTypes();

  /**
   * Returns the map from implementations to procedures.
   * @return the map from implementations to procedures
   */
  UsageToDefMap<Implementation, Procedure> getImplProc();

  /**
   * Returns the map from implementation parameters to procedure parameters.
   * @return the map from implementation parameters to procedure parameters
   */
  UsageToDefMap<VariableDecl, VariableDecl> getParamMap();

  /**
   * Returns the symbol table.
   * @return the symbol table
   */
  SymbolTable getST(); 

  /**
   * Returns the (possibly modified) AST that was last processed.
   * @return the last processed AST
   */
  Declaration getAST();
  
}

