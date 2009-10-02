package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$FontWeight extends CSS$CssValue {
    
    CSS$FontWeight() {
        
    }
    
    int getValue() {
        return weight;
    }
    
    Object parseCssValue(String value) {
        CSS$FontWeight fw = new CSS$FontWeight();
        fw.svalue = value;
        if (value.equals("bold")) {
            fw.weight = 700;
        } else if (value.equals("normal")) {
            fw.weight = 400;
        } else {
            try {
                fw.weight = Integer.parseInt(value);
            } catch (NumberFormatException nfe) {
                fw = null;
            }
        }
        return fw;
    }
    
    Object fromStyleConstants(StyleConstants key, Object value) {
        if (value.equals(Boolean.TRUE)) {
            return parseCssValue("bold");
        }
        return parseCssValue("normal");
    }
    
    Object toStyleConstants(StyleConstants key, View v) {
        return (weight > 500) ? Boolean.TRUE : Boolean.FALSE;
    }
    
    boolean isBold() {
        return (weight > 500);
    }
    int weight;
}
