package input;

import java.io.IOException;

import input.intf.SuggestListener;
import input.intf.SuggestReporter;

/**
 * @author Kj
 *
 */
public class InputTest {

	public static void main(String[] args) {
		SuggestReporter rep = new SuggestReporterImpl();
		rep.addListener(new SuggestListener(){

			public void suggest(Suggestion suggestion) {
				System.out.println("Got ");
			}

			public void finished() {
				// TODO Auto-generated method stub
				
			}
			
		});
		try {
			rep.runFromFile("in.txt");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
