package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$CssValue implements Serializable {
    
    CSS$CssValue() {
        
    }
    
    Object parseCssValue(String value) {
        return value;
    }
    
    Object parseHtmlValue(String value) {
        return parseCssValue(value);
    }
    
    Object fromStyleConstants(StyleConstants key, Object value) {
        return null;
    }
    
    Object toStyleConstants(StyleConstants key, View v) {
        return null;
    }
    
    public String toString() {
        return svalue;
    }
    String svalue;
}
