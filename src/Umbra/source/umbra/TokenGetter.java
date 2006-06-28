/*
 * Created on 2005-05-13
 */
package umbra;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.swt.graphics.RGB;

import umbra.ColorManager;
import umbra.IColorValues;
import umbra.NonRuleBasedDamagerRepairer;

/**
 * This method collects array of colors from IColorValues interface
 * and returns them as a token array
 * 
 * @author Wojtek W¹s
 */
public class TokenGetter {

	static int CN = 4;
	
	/**
	 * @param manager	Color manager related to the editor
	 * @param mod		Number of current coloring style
	 * @param i			Position in array of color values
	 * @return			Color value as a token
	 */
	
	static public IToken getToken(ColorManager manager, int mod, int i) {
		return new Token(getTextAttribute(manager, mod, i));
	}
	
	/**
	 * @param manager	Color manager related to the editor
	 * @param mod		Number of current coloring style
	 * @return			Array of tokens for each color value
	 * 					(for each window element to be coloured)
	 */
	
	static public IToken[] getTokenTab(ColorManager manager, int mod) {
		IToken[] tokens = new IToken[IColorValues.PARTS];
		for (int i = 0; i < IColorValues.PARTS; i++) {
			tokens[i] = TokenGetter.getToken(manager, mod, i);
		}
		return tokens;
	}
	
	static public NonRuleBasedDamagerRepairer getRepairer(ColorManager manager, int mod, int i) {
		return new NonRuleBasedDamagerRepairer(getTextAttribute(manager, mod, i));
	}
	
	/**
	 * @param manager	Color manager related to the editor
	 * @param mod		Number of current coloring style
	 * @param i			Position in array of color values
	 * @return			Particular color as an attribute 					
	 */
	
	private static TextAttribute getTextAttribute(ColorManager manager, int mod, int i) {
		return new TextAttribute(manager.getColor(new RGB(IColorValues.models[mod][CN * i], 
				IColorValues.models[mod][(CN * i) + 1], IColorValues.models[mod][(CN * i) + 2])), 
				null, IColorValues.models[mod][(CN * i) + 3]);
	}			
}
