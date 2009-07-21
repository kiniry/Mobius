package freeboogie.dumpers;

import java.io.StringWriter;

import genericutils.*;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.tc.TcInterface;

/**
 * Dumps flow graphs for all implementations in dot format.
 *
 * @author rgrig 
 */
@SuppressWarnings("unused") // unused parameters
public class FlowGraphDumper extends Transformer {
  private String cmdToString(Command c) {
    StringWriter sw = new StringWriter();
    PrettyPrinter pp = new PrettyPrinter(sw);
    c.eval(pp);
    return sw.toString();
  }

  @Override
  public void see(
    Implementation implementation,
    Attribute attr,
    Signature sig,
    Body body,
    Declaration tail
  ) {
    SimpleGraph<Block> fg = tc.getFlowGraph(implementation);
    System.out.println("digraph \"" + implementation.getSig().getName() + "@" + implementation.loc() + "\" {");
    if (body.getBlocks() != null)
      System.out.println("  \"" + body.getBlocks().getName() + "\" [style=bold];");
    for (Block b : fg.nodesInTopologicalOrder()) {
      System.out.print("  \"" + b.getName() + "\" ");
      if (b.getCmd() == null)
        System.out.print("[shape=circle,label=\"\"]");
      else
        System.out.print("[shape=box,label=\""+cmdToString(b.getCmd())+"\"]");
      System.out.println(";");
    }
    fg.iterEdge(new Closure<Pair<Block,Block>>() {
      @Override public void go(Pair<Block,Block> t) {
        System.out.println("  \"" + t.first.getName() + "\" -> \"" 
          + t.second.getName() + "\";");
      }});
    System.out.println("}");
    if (tail != null) tail.eval(this);
  }
}
