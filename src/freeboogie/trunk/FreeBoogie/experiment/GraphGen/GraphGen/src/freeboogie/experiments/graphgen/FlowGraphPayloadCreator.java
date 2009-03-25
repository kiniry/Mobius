package freeboogie.experiments.graphgen;

public class FlowGraphPayloadCreator implements PayloadCreator<FlowGraphPayload> {

  public FlowGraphPayload createPayload() {
    return new FlowGraphPayload();
  }

}
