package b2bpl.bytecode;

import java.text.MessageFormat;


public class TroubleMessage {

  private final TroubleDescription description;

  private final Object[] parameters;

  private TroublePosition position;

  public TroubleMessage(TroubleDescription description, Object... parameters) {
    this(null, description, parameters);
  }

  public TroubleMessage(
      TroublePosition position,
      TroubleDescription description,
      Object... parameters) {
    this.description = description;
    this.parameters = parameters;
    this.position = position;
  }

  public TroublePosition getPosition() {
    return position;
  }

  public void setPosition(TroublePosition position) {
    this.position = position;
  }

  public TroubleDescription getDescription() {
    return description;
  }

  public Object[] getParameters() {
    return parameters;
  }

  public String getDescriptionString() {
    return MessageFormat.format(description.getDescription(), parameters);
  }
}
