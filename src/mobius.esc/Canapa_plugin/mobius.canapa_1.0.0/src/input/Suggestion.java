package input;

/**
 * @author Kjk
 */
public class Suggestion {
	public static final int STATIC_FIELD = 0;
	public static final int INSTANCE_FIELD = 1;
	public static final int PARAMETER = 2;
	public static final int LOCAL_VARIABLE = 3;
	public static final int METHOD_OVERRIDE = 4;
	public static final int METHOD = 5;

	private Location warningLoc;
	private Location suggestionLoc;
	private int type;
	private String text;

	public Suggestion(Location warningLoc, Location suggestionLoc, int type,
			String text) {
		this.warningLoc = warningLoc;
		this.suggestionLoc = suggestionLoc;
		this.type = type;
		this.text = text;
	}
	
	public Location getWarningLoc(){
		return warningLoc;
	}
	
	public Location getSuggestionLoc(){
		return suggestionLoc;
	}
	
	public int getType(){
		return type;
	}
	
	public String getText(){
		return text;
	}
}
