package freeboogie.experiments.graphgen;

import java.io.PrintStream;

public class FlowGraphPayload {

  private boolean read;
  private boolean write;
  private static int globalCnt = 0; // for printing boogie
  private final int cnt;
  
  public FlowGraphPayload() {
    this.read = false;
    this.write = false;
    this.cnt = globalCnt++;
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

  public void printBoogie(PrintStream ps) {
    ps.print(write? "x" : "dummy");
    ps.print(" := ");
    ps.print(read? "x" : "dummy");
    ps.print(" + " + cnt + ";");
  }
}
