public class Neuter {

  /*@ requires n instanceof GermanNoun || n instanceof GreekNoun;
    @ ensures \result <==> n.gender.equals("neuter");   @*/
  public boolean isNeuter(final Gendered n) {
    if (n instanceof GermanNoun) {
      GermanNoun gern = (GermanNoun) n;
      return !(gern.isFemale() || gern.isMale());
    } else {
      GreekNoun grkn = (GreekNoun) n;
      return !(grkn.isFemale() || grkn.isMale());
    }
  }
}
