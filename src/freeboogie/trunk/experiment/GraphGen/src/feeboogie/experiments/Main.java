package feeboogie.experiments;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;



public class Main {

  /**
   * @param args
   * @throws FileNotFoundException 
   */
  public static void main(String[] args) throws FileNotFoundException {
    
    FlowGraphPayloadCreator creator = new FlowGraphPayloadCreator();
    Counter counter = new Counter();
    
    Generator<FlowGraphPayload> generator = new Generator<FlowGraphPayload>();
    
    Graph<FlowGraphPayload> graph = generator.generate(0, 4, 100000, creator, counter);
    
    System.out.println("Created " + generator.getAllNodesList().size());
    
    GraphDotPrinter printer = new GraphDotPrinter(new PrintStream(new FileOutputStream("test.dot")), 1);
    printer.printNodes(generator.getAllNodesList());
    printer.finish();
    
//    printer = new GraphDotPrinter(System.out, 1);
//    printer.printNodes(generator.getAllNodesList());
//    printer.finish();
  }

}
