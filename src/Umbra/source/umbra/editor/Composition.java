/*
 * Created on 2005-05-14
 *
 */
package umbra.editor;

/**
 * This class is a static container that keeps the value of current coloring 
 * style that is obtained after each refreshing (which takes place when
 * a bytecode document is created too).
 * 
 * @author Wojtek Wąs
 */
public class Composition {
	
	/**
	 * The current value of the colouring style.
	 */
	static private int mod = 1;
	
	/**
	 * TODO
	 */
	static private boolean disas = false;
	
	/**
	 * @return if called during disassembling - the current
	 * coloring style value;
	 * otherwise - it means that bytecode editor is open
	 * with no relation to the source, therefore it is colored grey.
	 * TODO really? 
	 */
	static public int getMod() {
		if (!disas) return IColorValues.MODELS.length -1;
		return mod;
	}
	
	/**
	 * This method sets the current initial colouring style.
	 */
	static public void setMod(int i) {
		mod = i;
	}
		
	/**
	 * TODO strange???
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
