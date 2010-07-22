package ie.ucd.semanticproperties.plugin.api;

import ie.ucd.semanticproperties.plugin.exceptions.UnknownScopeException;

public enum ScopeId {

  FILE("File", "file"),
  MODULE("Module", "module", "class", "type"),
  FEATURE("Feature", "feature", "method", "field"),
  VARIABLE("var", "variable"),
  ALL("all");

  private final String[] names;

  private ScopeId(String... names) {
    this.names = names;
  }

  public static ScopeId scopeIdFor(String name) throws UnknownScopeException {
    for (ScopeId id : ScopeId.values()) {
      for (String n : id.names) {
        if (n.equals(name)) {
          return id;
        }
      }
    }
    throw new UnknownScopeException();
  }

}
