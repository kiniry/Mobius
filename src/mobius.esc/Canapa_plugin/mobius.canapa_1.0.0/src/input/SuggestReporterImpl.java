package input;

import input.intf.SuggestListener;
import input.intf.SuggestReporter;
import input.parser.SuggestionParser;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import logs.Log;
import logs.LogType;

/**
 * @author Kjk
 */

public class SuggestReporterImpl implements SuggestReporter {

	private static final int STATE_NONE = 0;
	private static final int STATE_NULL_WARNING = 1;
	private static final int STATE_NONNULL_WARNING = 2;
	private static final int NULL_SUGGEST_LINE = 3;
	private static final int NONNULL_SUGGEST_LINE = 6;

	private static String WARNING = ": Warning:";
	private static String WARNING_NULL = "(Null)";
	private static String WARNING_NONNULL = "(NonNull)";
	private static String SEPARATOR = ":";

	private List listeners = new LinkedList();

	private int state = STATE_NONE;
	private int counter;

	private Location warningLoc;

	private static String getFileNameFromWarning(String line) {
		return line.substring(0,line.lastIndexOf(SEPARATOR));
	}

	private static String getLineNoFromWarning(String line) {
		String l = line.substring(line.indexOf(SEPARATOR) + 1);
		l = l.substring(0, l.indexOf(SEPARATOR));
		return l;
	}

	private String searchWarning(String line, String pattern){
		try {
			int warning = line.indexOf(WARNING);
			if (warning == -1)
				return null;
			String l = line.substring(warning+WARNING.length()+1);
			if (l.indexOf(pattern) == -1)
				return null;
			Log.println(LogType.INPUT, "-------------------------------");
			Log.println(LogType.INPUT, "Warning line: \"" + line + "\"");
			String file = getFileNameFromWarning(line.substring(0, warning));
			Log.println(LogType.INPUT, "File = \"" + file + "\"");
			return file;
		} catch (Exception e) {
			return null;
		}
	}
	
	private String searchNullWarning(String line) {
		String result = searchWarning(line, WARNING_NULL);
		if (result!=null)
			state = STATE_NULL_WARNING;
		return result;
	}
	
	private String searchNonNullWarning(String line) {
		String result = searchWarning(line, WARNING_NONNULL);
		if (result!=null)
			state = STATE_NONNULL_WARNING;
		return result;
	}
	private void processLine(String line) {
		Log.println(LogType.INPUT, "Processing line \""+ line+"\"");
		SuggestionParser p = new SuggestionParser();
		String file = null;
		switch (state) {
		case STATE_NONE:
			file = searchNullWarning(line);
			if (file==null)
				file = searchNonNullWarning(line);
			counter = 0;
			break;
		case STATE_NULL_WARNING:
			counter++;
			if (counter==NULL_SUGGEST_LINE){
				counter=0;
				state = STATE_NONE;
				informListeners(p.tryProcessSuggestion(file, line));
			}
			break;
		case STATE_NONNULL_WARNING:
			counter++;
			if (counter==NONNULL_SUGGEST_LINE){
				counter=0;
				state = STATE_NONE;
				informListeners(p.tryProcessSuggestion(file, line));
			}
			break;
		}
	}

	public void addListener(SuggestListener listener) {
		listeners.add(listener);
	}

	public void run(String s) {
		Log.println(LogType.INPUT, "Running from string");
		String[] lines = s.split("\n");
		for (int i = 0; i < lines.length; i++)
			processLine(lines[i]);
		finished();
	}

	public void runFromFile(String file) throws IOException {
		Log.println(LogType.INPUT, "Running from file");
		BufferedReader bfr = new BufferedReader(new FileReader(file));
		String line;
		while ((line = bfr.readLine()) != null)
			processLine(line);
		finished();
	}

	private void informListeners(Suggestion s){
		if (s!=null){
			Iterator it = listeners.iterator();
			while (it.hasNext()){
				((SuggestListener)it.next()).suggest(s);
			}
		}
	}
	
	private void finished(){
		Iterator it = listeners.iterator();
		while (it.hasNext()){
			((SuggestListener)it.next()).finished();
		}
	}
}
