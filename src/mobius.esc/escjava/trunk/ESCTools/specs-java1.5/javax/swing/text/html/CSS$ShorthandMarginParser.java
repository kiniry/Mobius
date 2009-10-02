package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$ShorthandMarginParser {
    
    CSS$ShorthandMarginParser() {
        
    }
    
    static void parseShorthandMargin(CSS css, String value, MutableAttributeSet attr, CSS$Attribute[] names) {
        String[] strings = CSS.parseStrings(value);
        int count = strings.length;
        int index = 0;
        switch (count) {
        case 0: 
            return;
        
        case 1: 
            for (int counter = 0; counter < 4; counter++) {
                css.addInternalCSSValue(attr, names[counter], strings[0]);
            }
            break;
        
        case 2: 
            css.addInternalCSSValue(attr, names[0], strings[0]);
            css.addInternalCSSValue(attr, names[2], strings[0]);
            css.addInternalCSSValue(attr, names[1], strings[1]);
            css.addInternalCSSValue(attr, names[3], strings[1]);
            break;
        
        case 3: 
            css.addInternalCSSValue(attr, names[0], strings[0]);
            css.addInternalCSSValue(attr, names[1], strings[1]);
            css.addInternalCSSValue(attr, names[2], strings[2]);
            css.addInternalCSSValue(attr, names[3], strings[1]);
            break;
        
        default: 
            for (int counter = 0; counter < 4; counter++) {
                css.addInternalCSSValue(attr, names[counter], strings[counter]);
            }
            break;
        
        }
    }
}
