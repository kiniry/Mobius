package engine;

import input.Suggestion;
import canapa.util.FixLocation;

public class ModifierFixLocation implements FixLocation {

	private Suggestion _suggestion;
	private ModifiedFile _file;
	
	public ModifierFixLocation(Suggestion suggestion, ModifiedFile file) {
		_suggestion = suggestion;
		_file = file;
	}

	public String getSuggestion() {
		return "/*CANAPA*//*@ non_null @*/";
	}

	public int getSuggestionType() {
		return _suggestion.getType();
	}

	public String getFile() {
		return _suggestion.getSuggestionLoc().getFile();
	}

	public int getLine() {
		return _suggestion.getSuggestionLoc().getLine();
	}

	public int getColumn() {
		return _suggestion.getSuggestionLoc().getCol()
			+ _file.getLineOffset(getLine());
	}

}
