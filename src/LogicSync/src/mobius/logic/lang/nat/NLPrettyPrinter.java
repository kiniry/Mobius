package mobius.logic.lang.nat;

import java.io.PrintStream;
import java.util.List;

import mobius.logic.lang.nat.ast.AEvaluator;
import mobius.logic.lang.nat.ast.Item;
import mobius.logic.lang.nat.ast.Logic;

public class NLPrettyPrinter extends AEvaluator<String> {

  private final PrintStream ps;
  
  public NLPrettyPrinter(PrintStream ps) {
    this.ps = ps;
  }
  
  public void closeStream() {
    ps.close();
  }
  
  @Override
  public String evalItem(String id, String description) {
    ps.print(id);
    ps.print(':');
    ps.print("  ");
    ps.print(description);
    return null;
  }

  @Override
  public String evalLogic(String name, List<Item> items) {
    ps.print("logic ");
    ps.println(name);
    for (Item item : items) {
      ps.print("  ");
      item.eval(this);
      ps.println();
    }
    ps.println("end");
    return null;
  }

  @Override
  public String evalProgram(List<Logic> logics) {
    for (Logic logic : logics) {
      logic.eval(this);
      ps.println();
      ps.println();
    }
    return null;
  }

}
