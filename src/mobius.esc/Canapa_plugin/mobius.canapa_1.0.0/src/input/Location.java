/*
 * Created on 2005-12-19
 */
package input;

import ui.Main;

/**
 * @author Kjk
 */
public class Location {
	private String file;
	private int line;
	private int col;
	
	public Location(String file, int line, int col){
		this.file = Main.volume + file;
		this.line = line;
		this.col = col;
	}
	
	public String getFile(){
		return file;
	}

	public int getLine(){
		return line;
	}

	public int getCol(){
		return col;
	}	
}
