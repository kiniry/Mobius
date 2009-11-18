package ie.ucd.bon.tester;

import ie.ucd.bon.API;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;

public class BONTestWrapper implements ToolTestWrapper {

  @Override
  public void run(String input) {
    ParseResult result = API.parse(input);
    ParsingTracker tracker = new ParsingTracker();
    tracker.addParse(null, result);
    if (result.isValidParse()) {
      API.typeCheck(tracker, true, true, true, true, false);
    }
//    Problems tcProblems = API.typeCheck(tracker, true, true, true, true, false);
//    Problems pProblems = tracker.getErrorsAndWarnings();
//    Problems totalProblems = new Problems("Spoof");
//    totalProblems.addProblems(pProblems).addProblems(tcProblems);
//    System.out.println(totalProblems.getNumberOfErrors() + " errors.");
  }

}
