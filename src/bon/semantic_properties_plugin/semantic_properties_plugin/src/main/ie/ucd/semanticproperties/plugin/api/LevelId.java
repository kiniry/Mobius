package ie.ucd.semanticproperties.plugin.api;

import ie.ucd.semanticproperties.plugin.exceptions.UnknownLevelException;

public enum LevelId {

  BON_INFORMAL("bon_informal"),
  BON_FORMAL("bon", "bon_formal"),
  JAVA_JML("java", "java_jml");

  private final String[] names;

  private LevelId(String... names) {
    this.names = names;
  }

  public static LevelId levelIdFor(String name) throws UnknownLevelException {
    for (LevelId id : LevelId.values()) {
      for (String n : id.names) {
        if (n.equals(name)) {
          return id;
        }
      }
    }
    throw new UnknownLevelException();
  }

}
