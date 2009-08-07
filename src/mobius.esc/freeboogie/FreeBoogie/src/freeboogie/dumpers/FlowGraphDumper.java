package freeboogie.dumpers;

import java.io.*;

import com.google.common.base.Preconditions;
import genericutils.*;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.tc.TcInterface;

/**
 * Dumps flow graphs for all implementations in dot format.
 *
 * TODO: Move to freeboogie.astutil and remove this package.
 *
 * @author rgrig 
 */
@SuppressWarnings("unused") // unused parameters
public class FlowGraphDumper extends Transformer {
  private File directory;

  public void directory(File directory) {
    Preconditions.checkArgument(directory.exists());
    this.directory = directory;
  }

  private String cmdToString(Command c) {
    StringWriter sw = new StringWriter();
    PrettyPrinter pp = new PrettyPrinter();
    pp.writer(sw);
    c.eval(pp);
    return sw.toString();
  }

  @Override
  public void see(
    Implementation impl,
    Attribute attr,
    Signature sig,
    Body body,
    Declaration tail
  ) {
    String name = 
      impl.getSig().getName() + 
      "_at_" + 
      impl.loc().toString().replaceAll(":", "-");
    try {
      final PrintWriter w = new PrintWriter(new File(directory, name));
      SimpleGraph<Block> fg = tc.getFlowGraph(impl);
      w.println("digraph \"" + name + "\" {");
      if (body.getBlocks() != null)
        w.println("  \"" + body.getBlocks().getName() + "\" [style=bold];");
      for (Block b : fg.nodesInTopologicalOrder()) {
        w.print("  \"" + b.getName() + "\" ");
        if (b.getCmd() == null)
          w.print("[shape=circle,label=\"\"]");
        else
          w.print("[shape=box,label=\""+cmdToString(b.getCmd())+"\"]");
        w.println(";");
      }
      fg.iterEdge(new Closure<Pair<Block,Block>>() {
        @Override public void go(Pair<Block,Block> t) {
          w.println("  \"" + t.first.getName() + "\" -> \"" 
            + t.second.getName() + "\";");
        }});
      w.println("}");
      w.flush();
      w.close();
    } catch (FileNotFoundException e) {
      assert false : "PrintWriter should create the file.";
    }
    if (tail != null) tail.eval(this);
  }
}
