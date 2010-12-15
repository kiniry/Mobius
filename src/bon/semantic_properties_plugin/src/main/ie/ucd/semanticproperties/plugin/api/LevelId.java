package ie.ucd.semanticproperties.plugin.api;

import ie.ucd.semanticproperties.plugin.exceptions.UndefinedLevelException;
import ie.ucd.semanticproperties.plugin.exceptions.UndefinedScopeException;
/**
 * Sets the allowable levels for semantic property levels and instances.
 * @author eo
 *
 */
public enum LevelId {

  BON_INFORMAL("bon_informal"),
  BON_FORMAL("bon", "bon_formal"),
  JAVA_JML("java", "java_jml");

  /**
   * List of all names for this LevelId.
   */
  private final String[] names;

  /**
   * Constructor for LevelId.
   * @param names The variations of names for this LevelId
   */
  private LevelId(String... names) {
    this.names = names;
  }

  /**
   * Returns the level if one exists for input string.
   * @param name Input string.
   * @return Scope
   * @throws UndefinedLevelException if no level exists for this input string.
   */
  public static LevelId levelIdFor(String name) throws UndefinedLevelException {
    for (LevelId id : LevelId.values()) {
      for (String n : id.names) {
        if (n.equals(name)) {
          return id;
        }
      }
    }
    throw new UndefinedLevelException();
  }

}
