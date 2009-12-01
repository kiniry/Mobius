package escjava.plugin.actions;

public class CheckWithSimplify extends Check {
  public CheckWithSimplify() {
    setProver(Prover.simplify);
  }
}
