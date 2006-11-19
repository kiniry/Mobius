/*
 * Created on 2005-05-14
 *
 */
package umbra.editor;

/**
 * This class keeps the value of current coloring style
 * that is obtained after each refreshing.
 * 
 * @author Wojtek Wąs
 */
public class Composition {
	
	/**
	 * TODO
	 */
	static int mod = 1;
	/**
	 * TODO
	 */
	static boolean disas = false;
	
	/**
	 * @return if called during disassembling - the current
	 * coloring style value;
	 * otherwise - it means that bytecode editor is open
	 * with no relation to the source, therefore it is colored grey. 
	 */
	static public int getMod() {
		if (!disas) return IColorValues.models.length -1;
		return mod;
	}
	
	/**
	 * TODO
	 */
	static public void setMod(int i) {
		mod = i;
	}
		
	/**
	 * TODO
	 */
	static public void startDisas() {
		disas = true;
	}
	
	/**
	 * TODO
	 */
	static public void stopDisas() {
		disas = false;
	}

}
