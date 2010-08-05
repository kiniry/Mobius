package ie.ucd.semanticproperties.plugin.api;

import ie.ucd.semanticproperties.plugin.exceptions.UnknownScopeException;
/**
 * Sets the allowable scopes for levels and instances.
 * @author eo
 *
 */
public enum ScopeId {

  FILE("File", "file"),
  MODULE("Module", "module", "class", "type"),
  FEATURE("Feature", "feature", "method", "field"),
  VARIABLE("var", "variable"),
  ALL("all");

  /**
   * list of names for this ScopeId.
   */
  private final String[] names;

  /**
   * Constructor for ScopeId.
   * @param names The variations of names for this scopeId.
   */
  private ScopeId(String... names) {
    this.names = names;
  }

  /**
   * Returns the scope if one exists for input string.
   * @param name Input string.
   * @return Scope
   * @throws UnknownScopeException if no scope exists for this input string.
   */
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
