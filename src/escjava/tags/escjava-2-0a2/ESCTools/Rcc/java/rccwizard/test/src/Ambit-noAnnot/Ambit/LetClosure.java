// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Ambit;

public class LetClosure extends Result {

  private String ide;
  public IdeList params;
  public CodeProc body;
  public Env env;

  private LetClosure(String ide, IdeList params, CodeProc body, Env env) {
    this.ide = ide;
    this.params = params;
    this.body = body;
    this.env = env;        
  }
  
  public static Env ConsLet(String ide, IdeList params, CodeProc body, Env env) {
    LetClosure closure = new LetClosure(ide, params, body, env);
    return new EnvCons(ide, closure, env);
  }
    
  public String toString() {
    return "<defined " + ide + ">";
  }

}
