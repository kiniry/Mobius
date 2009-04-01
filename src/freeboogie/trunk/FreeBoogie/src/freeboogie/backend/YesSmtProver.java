package freeboogie.backend;

/** 
 * A prover that says everything is OK.
 * Used for debugging.
 */
public class YesSmtProver extends Prover<SmtTerm> {
  public YesSmtProver() {
    builder = new SmtTermBuilder();
  }

  @Override
  public void sendAssume(SmtTerm t) {
    analyzeSmtTerm("assume", t);
  }

  @Override
  public void sendRetract() {}

  @Override
  public boolean isValid(SmtTerm t) {
    analyzeSmtTerm("assert", t);
    return true;
  }

  @Override
  public String[][] getLabels() { return new String[0][]; }

  @Override
  public void terminate() {}

  private void analyzeSmtTerm(String prefix, SmtTerm s) {
    SmtTerm u = SmtTerms.eliminateSharing(s, builder);
    System.out.printf("DUMMYPROVER %s %d %d %d\n", prefix, Statistics.nodesCount(s), Statistics.printSize(s), Statistics.printSize(u));
  }
}
