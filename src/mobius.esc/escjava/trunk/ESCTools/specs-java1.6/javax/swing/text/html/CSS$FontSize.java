package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$FontSize extends CSS$CssValue {
    /*synthetic*/ final CSS this$0;
    
    CSS$FontSize(/*synthetic*/ final CSS this$0) {
        this.this$0 = this$0;
        
    }
    
    float getValue(AttributeSet a, StyleSheet ss) {
        ss = CSS.access$300(this$0, ss);
        if (index) {
            return this$0.getPointSize((int)value, ss);
        } else if (lu == null) {
            return value;
        } else {
            if (lu.type == 0) {
                boolean isW3CLengthUnits = (ss == null) ? false : ss.isW3CLengthUnits();
                return lu.getValue(isW3CLengthUnits);
            }
            if (a != null) {
                AttributeSet resolveParent = a.getResolveParent();
                if (resolveParent != null) {
                    int pValue = StyleConstants.getFontSize(resolveParent);
                    float retValue;
                    if (lu.type == 1 || lu.type == 3) {
                        retValue = lu.value * (float)pValue;
                    } else {
                        retValue = lu.value + (float)pValue;
                    }
                    return retValue;
                }
            }
            return 12;
        }
    }
    
    Object parseCssValue(String value) {
        CSS$FontSize fs = new CSS$FontSize(this$0);
        fs.svalue = value;
        try {
            if (value.equals("xx-small")) {
                fs.value = 1;
                fs.index = true;
            } else if (value.equals("x-small")) {
                fs.value = 2;
                fs.index = true;
            } else if (value.equals("small")) {
                fs.value = 3;
                fs.index = true;
            } else if (value.equals("medium")) {
                fs.value = 4;
                fs.index = true;
            } else if (value.equals("large")) {
                fs.value = 5;
                fs.index = true;
            } else if (value.equals("x-large")) {
                fs.value = 6;
                fs.index = true;
            } else if (value.equals("xx-large")) {
                fs.value = 7;
                fs.index = true;
            } else {
                fs.lu = new CSS$LengthUnit(value, (short)1, 1.0F);
            }
        } catch (NumberFormatException nfe) {
            fs = null;
        }
        return fs;
    }
    
    Object parseHtmlValue(String value) {
        CSS$FontSize fs = new CSS$FontSize(this$0);
        fs.svalue = value;
        try {
            int baseFontSize = this$0.getBaseFontSize();
            if ((value != null) && (value.charAt(0) == '+')) {
                int relSize = Integer.valueOf(value.substring(1)).intValue();
                fs.value = baseFontSize + relSize;
                fs.index = true;
            } else if ((value != null) && (value.charAt(0) == '-')) {
                int relSize = -Integer.valueOf(value.substring(1)).intValue();
                fs.value = baseFontSize + relSize;
                fs.index = true;
            } else {
                fs.value = Integer.parseInt(value);
                if (fs.value > 7) {
                    fs.value = 7;
                } else if (fs.value < 0) {
                    fs.value = 0;
                }
                fs.index = true;
            }
        } catch (NumberFormatException nfe) {
            fs = null;
        }
        return fs;
    }
    
    Object fromStyleConstants(StyleConstants key, Object value) {
        if (value instanceof Number) {
            CSS$FontSize fs = new CSS$FontSize(this$0);
            fs.value = CSS.getIndexOfSize(((Number)(Number)value).floatValue(), StyleSheet.sizeMapDefault);
            fs.svalue = Integer.toString((int)fs.value);
            fs.index = true;
            return fs;
        }
        return parseCssValue(value.toString());
    }
    
    Object toStyleConstants(StyleConstants key, View v) {
        if (v != null) {
            return new Integer((int)getValue(v.getAttributes(), null));
        }
        return new Integer((int)getValue(null, null));
    }
    float value;
    boolean index;
    CSS$LengthUnit lu;
}
