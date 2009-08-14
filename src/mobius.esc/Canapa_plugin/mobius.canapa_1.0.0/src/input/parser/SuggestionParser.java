package input.parser;

import input.Location;
import input.Suggestion;
import logs.Log;
import logs.LogType;

/**
 * @author Kjk
 */
public class SuggestionParser {

	private static final char SUGGESTION_POSITION_BEG = '[';
	private static final char SUGGESTION_POSITION_SEP = ',';
	private static final char SUGGESTION_POSITION_END = ']';
	private static final char SUGGESTION_SEPARATOR = ':';
	private static final char SUGGESTION_NAME_SEPARATOR = '\'';
	private static final String PERHAPS_DECLARE = "perhaps declare ";
	private static final String[] DECLARE_WHAT = { "static field ",
			"instance field ", "parameter ", "local variable ",
			"method override ", "method " };	
	private static final String AT = "at ";
	private static final String IN = "in ";
	private static final String WITH = "with ";

	private int getSuggestionType(String suggestion) {
		for (int i=0; i<DECLARE_WHAT.length; i++)
			if (suggestion.indexOf(DECLARE_WHAT[i]) == 0)
				return i;
		return -1;
	}

	private Location tryGetWarningLoc(String warningFileName, String line) {
		try {
			int beg = line.indexOf(SUGGESTION_POSITION_BEG) + 1;
			int sep = line.indexOf(SUGGESTION_POSITION_SEP);
			int end = line.indexOf(SUGGESTION_POSITION_END);
			Log.println(LogType.SUG_PARSE, "Line = " + line.substring(beg, sep));
			Log.println(LogType.SUG_PARSE, "Col = " + line.substring(sep + 1, end));

			int lineNo = new Integer(line.substring(beg, sep)).intValue();
			int colNo = new Integer(line.substring(sep + 1, end)).intValue();
			return new Location(warningFileName, lineNo, colNo);
		} catch (Exception e) {
			return null;
		}
	}

	private Suggestion tryNormalSuggestion(Location warningLoc, String suggestion, int type){
		try{
			suggestion = suggestion.substring(PERHAPS_DECLARE.length()+DECLARE_WHAT[type].length()+2);
			Log.println(LogType.SUG_PARSE, "Suggestion left: \"" + suggestion + "\"");
			//Name
			String name = suggestion.substring(0, suggestion.indexOf(SUGGESTION_NAME_SEPARATOR));
			Log.println(LogType.SUG_PARSE, "Name: \""+name+"\"");
			
			suggestion = suggestion.substring(suggestion.indexOf(SUGGESTION_NAME_SEPARATOR)+1);
			Log.println(LogType.SUG_PARSE, "Left: \""+suggestion+"\"");
			//At
			suggestion = suggestion.substring(suggestion.indexOf(AT)+AT.length());
			Log.println(LogType.SUG_PARSE, "Left: \""+suggestion+"\"");
			//LineNo
			String lineStr = suggestion.substring(0,suggestion.indexOf(SUGGESTION_POSITION_SEP));
			Log.println(LogType.SUG_PARSE, "LineNo: \""+lineStr+"\"");
			suggestion = suggestion.substring(suggestion.indexOf(SUGGESTION_POSITION_SEP)+1);
			Log.println(LogType.SUG_PARSE, "Left: \""+suggestion+"\"");
			//ColNo
			String colStr = suggestion.substring(0, suggestion.indexOf(" "));
			Log.println(LogType.SUG_PARSE, "ColNo: \""+colStr+"\"");
			int lineNo = new Integer(lineStr).intValue();
			int colNo = new Integer(colStr).intValue();
			suggestion = suggestion.substring(suggestion.indexOf(" ")+1);
			Log.println(LogType.SUG_PARSE, "Left: \""+suggestion+"\"");
			
			//In
			suggestion = suggestion.substring(suggestion.indexOf(IN)+IN.length());
			Log.println(LogType.SUG_PARSE, "Left: \""+suggestion+"\"");
			//FileName
			String file = suggestion.substring(0, suggestion.indexOf(" "));
			Log.println(LogType.SUG_PARSE, "File: \""+file+"\"");
			suggestion = suggestion.substring(suggestion.indexOf(" ")+1);
			Log.println(LogType.SUG_PARSE, "Left: \""+suggestion+"\"");
			//With
			suggestion = suggestion.substring(suggestion.indexOf(WITH)+WITH.length()+1);
			Log.println(LogType.SUG_PARSE, "Left: \""+suggestion+"\"");
			//Text
			String suggestionString = suggestion.substring(0,suggestion.indexOf("'"));
			Log.println(LogType.SUG_PARSE, "Left: \""+suggestionString+"\"");
			suggestion = suggestion.substring(suggestion.indexOf(",")+1);
			Log.println(LogType.SUG_PARSE, "Left: \""+suggestion+"\"");
			Location suggestionLoc = new Location(file, lineNo, colNo);
			return new Suggestion(warningLoc, suggestionLoc, type, suggestionString);
		} catch (Exception e){
			return null;
		}		
	}
	
	public Suggestion tryProcessSuggestion(String warningFileName, String line) {
		Log.println(LogType.SUG_PARSE, "Suggestion line: \"" + line + "\"");
		String suggestion = line;
		Location warningLoc = tryGetWarningLoc(warningFileName, line);
		if (warningLoc == null)
			return null;
		int pd = suggestion.indexOf(PERHAPS_DECLARE);
		if (pd >= 0){
			//declare
			String rest = suggestion.substring(pd + PERHAPS_DECLARE.length());
			int type = getSuggestionType(rest);
			if (type < 0)
				return null;	
			 suggestion= suggestion
				.substring(suggestion.indexOf(SUGGESTION_SEPARATOR) + 1);
			 return tryNormalSuggestion(warningLoc, suggestion, type);			
		} else {
			return null;
		}
	}
}
