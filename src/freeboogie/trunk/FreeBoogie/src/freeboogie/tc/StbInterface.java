package freeboogie.tc;

import java.util.List;

import freeboogie.ast.Declaration;

public interface StbInterface {
  List<FbError> process(Declaration ast);
  SymbolTable getST();
  GlobalsCollector getGC();
}
