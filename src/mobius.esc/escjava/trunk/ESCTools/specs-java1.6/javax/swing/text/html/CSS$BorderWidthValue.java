package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$BorderWidthValue extends CSS$LengthValue {
    
    CSS$BorderWidthValue(String svalue, int index) {
        
        this.svalue = svalue;
        span = values[index];
        percentage = false;
    }
    
    Object parseCssValue(String value) {
        if (value != null) {
            if (value.equals("thick")) {
                return new CSS$BorderWidthValue(value, 2);
            } else if (value.equals("medium")) {
                return new CSS$BorderWidthValue(value, 1);
            } else if (value.equals("thin")) {
                return new CSS$BorderWidthValue(value, 0);
            }
        }
        return super.parseCssValue(value);
    }
    
    Object parseHtmlValue(String value) {
        if (value == HTML.NULL_ATTRIBUTE_VALUE) {
            return parseCssValue("medium");
        }
        return parseCssValue(value);
    }
    private static final float[] values = {1, 2, 4};
}
