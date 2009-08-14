/*
 * Created on 2005-12-18
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package canapa.util;

/**
 * @author Admin
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class FakeLocation implements FixLocation {

	public String getSuggestion() {
		return "/* nowa sugestia */";
	}

	public int getSuggestionType() {
		// TODO Auto-generated method stub
		return 0;
	}

	public String getFile() {
		// TODO Auto-generated method stub
		return null;
	}

	public int getLine() {
		return 37;
	}

	public int getColumn() {
		return 55;
	}

}
