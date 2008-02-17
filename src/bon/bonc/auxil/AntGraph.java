import net.ggtools.grand.output.DotWriter;
import net.ggtools.grand.ant.AntProject;

import java.io.File;

public class AntGraph {

	public static void main(String[] args) {
		try {		
		if (args.length > 1) {
			DotWriter dw = new DotWriter();
			dw.setProducer(new AntProject(new File(args[0])));
			dw.write(new File(args[1]));
		}
		} catch (Exception e) {
			System.out.println("Error: " + e);
		}
	}

}
