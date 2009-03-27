package freeboogie.experiments.graphgen;
import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.File;
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
    double splitProb = opt.getprobability_split();
    double linkProb = opt.getprobability_link();
    double readProb = opt.getprobability_read();
    double writeProb = opt.getprobability_write();
    
    FlowGraphPayloadCreator creator = new FlowGraphPayloadCreator();
    Counter counter = new Counter();
    //Generate
    Generator<FlowGraphPayload> generator = new Generator<FlowGraphPayload>(splitProb, linkProb);
    generator.generate(0, maxDepth, maxNodes, creator, counter);
    int totalNodes = generator.getAllNodesList().size();
    System.out.println("Created " + totalNodes);
    //Decorate
    FlowGraphDecorator decorator = new FlowGraphDecorator(readProb, writeProb);
    decorator.decorate(generator.getAllNodesList());
    int numReads = decorator.getReadCount();
    int numWrites = decorator.getWriteCount();
    System.out.println("Decorated " + numReads + " reads and " + numWrites + " writes.");
    System.out.println("That's " + (numReads * 100 / totalNodes) + "% reads and " + (numWrites * 100 / totalNodes) + "% writes.");

    //Print .dot?
    if (opt.isdot_output_fileSet()) {
      File dotOut = opt.getdot_output_file();
      System.out.println("Printing .dot to " + dotOut);
      GraphDotPrinter<FlowGraphPayload> printer = new FlowGraphDotPrinter(new PrintStream(new FileOutputStream(dotOut)));
      printer.printNodes(generator.getAllNodesList());
      printer.finish();
    }
    
    //Print boogie?
    if (opt.isboogie_output_fileSet()) {
      File boogieOut = opt.getboogie_output_file();
      System.out.println("Printing boogie to " + boogieOut);
      GraphBoogiePrinter.printBoogie(new PrintStream(new FileOutputStream(boogieOut)), generator.getAllNodesList());
    }
  }

}
