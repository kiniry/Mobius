package input.intf;

import input.Suggestion;

/**
 * @author Kjk
 */
public interface SuggestListener {
	void suggest(Suggestion suggestion);
	void finished();
}
