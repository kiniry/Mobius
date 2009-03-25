package freeboogie.experiments.graphgen;
import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

import freeboogie.experiments.graphgen.clops.GraphGenOptionsInterface;
import freeboogie.experiments.graphgen.clops.GraphGenParser;



public class Main {

  /**
   * @param args
   * @throws FileNotFoundException 
   */
  public static void main(String[] args) throws FileNotFoundException {
    
    GraphGenParser parser;
    try {
      parser = new GraphGenParser();
    } catch (InvalidOptionPropertyValueException e) {
      e.printStackTrace();
      return;
    }
    
    try {
      if (!parser.parse(args)) {
        System.err.println("Invalid options.");
        return;
      }
    } catch (AutomatonException e) {
      e.printStackTrace();
    } catch (InvalidOptionValueException e) {
      e.printStackTrace();
    }
    
    final GraphGenOptionsInterface opt = parser.getOptionStore();
    
    int maxDepth = opt.getmax_depth();
    int maxNodes = opt.getmax_nodes();
    
    FlowGraphPayloadCreator creator = new FlowGraphPayloadCreator();
    Counter counter = new Counter();
    
    Generator<FlowGraphPayload> generator = new Generator<FlowGraphPayload>();
    
    Graph<FlowGraphPayload> graph = generator.generate(0, maxDepth, maxNodes, creator, counter);
    
    System.out.println("Created " + generator.getAllNodesList().size());
    
    GraphDotPrinter printer = new GraphDotPrinter(new PrintStream(new FileOutputStream("test.dot")), 1);
    printer.printNodes(generator.getAllNodesList());
    printer.finish();
    
//    printer = new GraphDotPrinter(System.out, 1);
//    printer.printNodes(generator.getAllNodesList());
//    printer.finish();
  }

}
