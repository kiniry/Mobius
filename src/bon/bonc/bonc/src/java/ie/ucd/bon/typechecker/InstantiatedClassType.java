package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Type;

import java.util.Map;

public class InstantiatedClassType {

  public final Clazz clazz;
  public final Map<String,Type> bindersMap;
  public final Type type;

  public InstantiatedClassType(Clazz clazz, Map<String, Type> bindersMap, Type type) {
    this.bindersMap = bindersMap;
    this.clazz = clazz;
    this.type = type;
  }

  public Map<String, Type> getBindersMap() {
    return bindersMap;
  }

  public Type getType() {
    return type;
  }

  public Clazz getClazz() {
    return clazz;
  }
  
}
