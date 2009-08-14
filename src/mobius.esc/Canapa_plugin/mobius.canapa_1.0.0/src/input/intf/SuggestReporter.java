package input.intf;

import java.io.IOException;

/**
 * @author Kjk
 */
public interface SuggestReporter {
	void addListener(SuggestListener listener);
	void run(String s);
	void runFromFile(String file) throws IOException;
}
