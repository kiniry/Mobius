package escjava.plugin.actions;

public class CheckWithCvc3 extends Check {
  public CheckWithCvc3() {
    setProver(Prover.cvc3);
  }
  
  protected void setEnabled(boolean b) {
    if (!System.getProperty("os.name").startsWith("Linux")) {
      getAction().setEnabled(false);
    }
    else {
      super.setEnabled(b);
    }
  }      
}
