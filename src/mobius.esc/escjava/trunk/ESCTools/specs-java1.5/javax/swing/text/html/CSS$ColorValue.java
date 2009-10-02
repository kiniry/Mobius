package javax.swing.text.html;

import java.awt.Color;
import java.io.*;
import javax.swing.text.*;

class CSS$ColorValue extends CSS$CssValue {
    
    CSS$ColorValue() {
        
    }
    
    Color getValue() {
        return c;
    }
    
    Object parseCssValue(String value) {
        Color c = CSS.stringToColor(value);
        if (c != null) {
            CSS$ColorValue cv = new CSS$ColorValue();
            cv.svalue = value;
            cv.c = c;
            return cv;
        }
        return null;
    }
    
    Object parseHtmlValue(String value) {
        return parseCssValue(value);
    }
    
    Object fromStyleConstants(StyleConstants key, Object value) {
        CSS$ColorValue colorValue = new CSS$ColorValue();
        colorValue.c = (Color)(Color)value;
        colorValue.svalue = CSS.colorToHex(colorValue.c);
        return colorValue;
    }
    
    Object toStyleConstants(StyleConstants key, View v) {
        return c;
    }
    Color c;
}
