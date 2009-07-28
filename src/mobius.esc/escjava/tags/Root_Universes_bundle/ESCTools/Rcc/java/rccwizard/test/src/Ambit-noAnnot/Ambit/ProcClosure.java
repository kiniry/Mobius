// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class ProcClosure extends Result {

  private String ide;
  public CodeProc body;
  public Env env;

  private ProcClosure(String ide, CodeProc body, Env env) {
    this.ide = ide;
    this.body = body;
    this.env = env;        
  }
  
  public static Env ConsRec(String ide, CodeProc body, Env env) {
    ProcClosure closure = new ProcClosure(ide, body, null);
    Env recEnv = new EnvCons(ide, closure, env);
    closure.env = recEnv;
    return recEnv;
  }
    
  public String toString() {
    return "<process " + ide + ">";
  }

}
