/*
 * Created on 2005-04-30
 */
package umbra.editor.boogiepl;

/**
 * Some string arrays used to identify keywords and instruction
 * names in bytecode
 * 
 * @author Samuel Willimann
 */
public interface IBoogiePLStrings {

	/**
	 * TODO
	 */
	public static String[] instructions = new String[] { "assume", "assert", ":=", "goto", "return", "call",
		                                                 "procedure", "implementation", "returns", "int", "ref"};
	   
	/**
	 * TODO
	 */
	public static String[] jump = new String[] { "goto", "return" };

	/**
	 * TODO
	 */
	public static String[] call = new String[] { "call" };
	
	/**
	 * TODO
	 */
	public static String[] unary = new String[] { "assume", "assert" };
	
	/**
	 * TODO
	 */
	public static String[] binary = new String[] { ":=" };
	
	/**
	 * TODO
	 */
	public static String[] boogiePLKeywords = new String[] { "procedure", "implementation", "returns", "int", "ref" };	
}