package b2bpl.bytecode;


public class TroubleException extends RuntimeException {

  private static final long serialVersionUID = -3169227387084550319L;

  private final TroubleMessage troubleMessage;

  public TroubleException(TroubleMessage troubleMessage) {
    super(troubleMessage.getDescriptionString());
    this.troubleMessage = troubleMessage;
  }

  public TroubleMessage getTroubleMessage() {
    return troubleMessage;
  }
}
