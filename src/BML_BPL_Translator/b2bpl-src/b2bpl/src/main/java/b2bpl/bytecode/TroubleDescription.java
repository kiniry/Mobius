package b2bpl.bytecode;


public class TroubleDescription {

  private final Kind kind;

  private final String description;

  public TroubleDescription(Kind kind, String description) {
    this.kind = kind;
    this.description = description;
  }

  public Kind getKind() {
    return kind;
  }

  public String getDescription() {
    return description;
  }

  public static enum Kind {

    ERROR,

    WARNING;
  }
}
