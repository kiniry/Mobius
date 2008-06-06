package freeboogie.tc;

import java.util.*;
import freeboogie.ast.*;

/**
 * TODO: Describe this interface.
 * TODO: Move method comments from TypeChecker here
 */
public interface TcInterface {
  List<FbError> process(Declaration ast);
  SimpleGraph<Block> getFlowGraph(Implementation impl);
  Map<Expr, Type> getTypes();
  UsageToDefMap<Implementation, Procedure> getImplProc();
  UsageToDefMap<VariableDecl, VariableDecl> getParamMap();
  SymbolTable getST(); 
  Declaration getAST();
}
