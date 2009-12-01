package escjava.plugin.actions;

public class CheckWithCvc3 extends Check {
  public CheckWithCvc3() {
    setProver(Prover.cvc3);
  }
}
