// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

public class Args {

  public int argDispl;
  public Args next;

  public Args(int argDispl, Args next) {
    this.argDispl = Math.max(0, argDispl);
    this.next = next;
  }

}
