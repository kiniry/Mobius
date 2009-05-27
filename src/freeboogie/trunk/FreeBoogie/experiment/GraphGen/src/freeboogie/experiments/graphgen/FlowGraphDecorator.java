package freeboogie.experiments.graphgen;

import java.util.Collection;

public class FlowGraphDecorator {

  private final double probabilityRead;
  private final double probabilityWrite;
  
  private int readCount;
  private int writeCount;
  
  public FlowGraphDecorator(double probabilityRead, double probabilityWrite) {
    this.probabilityRead = probabilityRead;
        
    this.probabilityWrite = probabilityWrite;
    
    this.readCount = 0;
    this.writeCount = 0;
  }
  
  private boolean randomlySelectBoolean(double probabilityTrue) {
    return (Main.random.nextDouble() < probabilityTrue);
  }
  
  public void decorate(Node<FlowGraphPayload> node) {
    FlowGraphPayload payload = node.getPayload();
    payload.setRead(randomlySelectBoolean(probabilityRead));
    payload.setWrite(randomlySelectBoolean(probabilityWrite));
    
    readCount += payload.isRead() ? 1 : 0;
    writeCount += payload.isWrite() ? 1 : 0;
  }
  
  public void decorate(Collection<Node<FlowGraphPayload>> nodes) {
    for (Node<FlowGraphPayload> node : nodes) {
      decorate(node);
    }
  }

  public int getReadCount() {
    return readCount;
  }

  public int getWriteCount() {
    return writeCount;
  }
  
}
