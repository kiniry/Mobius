package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$FontFamily extends CSS$CssValue {
    
    CSS$FontFamily() {
        
    }
    
    String getValue() {
        return family;
    }
    
    Object parseCssValue(String value) {
        int cIndex = value.indexOf(',');
        CSS$FontFamily ff = new CSS$FontFamily();
        ff.svalue = value;
        ff.family = null;
        if (cIndex == -1) {
            setFontName(ff, value);
        } else {
            boolean done = false;
            int lastIndex;
            int length = value.length();
            cIndex = 0;
            while (!done) {
                while (cIndex < length && Character.isWhitespace(value.charAt(cIndex))) cIndex++;
                lastIndex = cIndex;
                cIndex = value.indexOf(',', cIndex);
                if (cIndex == -1) {
                    cIndex = length;
                }
                if (lastIndex < length) {
                    if (lastIndex != cIndex) {
                        int lastCharIndex = cIndex;
                        if (cIndex > 0 && value.charAt(cIndex - 1) == ' ') {
                            lastCharIndex--;
                        }
                        setFontName(ff, value.substring(lastIndex, lastCharIndex));
                        done = (ff.family != null);
                    }
                    cIndex++;
                } else {
                    done = true;
                }
            }
        }
        if (ff.family == null) {
            ff.family = "SansSerif";
        }
        return ff;
    }
    
    private void setFontName(CSS$FontFamily ff, String fontName) {
        ff.family = fontName;
    }
    
    Object parseHtmlValue(String value) {
        return parseCssValue(value);
    }
    
    Object fromStyleConstants(StyleConstants key, Object value) {
        return parseCssValue(value.toString());
    }
    
    Object toStyleConstants(StyleConstants key, View v) {
        return family;
    }
    String family;
}
