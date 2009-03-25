package freeboogie.experiments.graphgen;

public class FlowGraphPayload {

  private boolean read;
  private boolean write;
  
  public FlowGraphPayload() {
    this.read = false;
    this.write = false;
  }

  public boolean isRead() {
    return read;
  }

  public void setRead(boolean read) {
    this.read = read;
  }

  public boolean isWrite() {
    return write;
  }

  public void setWrite(boolean write) {
    this.write = write;
  }
  
}
