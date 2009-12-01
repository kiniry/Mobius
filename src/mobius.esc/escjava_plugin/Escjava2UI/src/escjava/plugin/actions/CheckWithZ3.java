package escjava.plugin.actions;

public class CheckWithZ3 extends Check {
  public CheckWithZ3() {
    setProver(Prover.z3);
  }
}
