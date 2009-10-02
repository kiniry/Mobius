package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$LengthValue extends CSS$CssValue {
    boolean mayBeNegative;
    
    CSS$LengthValue() {
        this(false);
    }
    
    CSS$LengthValue(boolean mayBeNegative) {
        
        this.mayBeNegative = mayBeNegative;
    }
    
    float getValue() {
        return getValue(false);
    }
    
    float getValue(boolean isW3CLengthUnits) {
        return getValue(0, isW3CLengthUnits);
    }
    
    float getValue(float currentValue) {
        return getValue(currentValue, false);
    }
    
    float getValue(float currentValue, boolean isW3CLengthUnits) {
        if (percentage) {
            return span * currentValue;
        }
        return CSS$LengthUnit.getValue(span, units, Boolean.valueOf(isW3CLengthUnits));
    }
    
    boolean isPercentage() {
        return percentage;
    }
    
    Object parseCssValue(String value) {
        CSS$LengthValue lv;
        try {
            float absolute = Float.valueOf(value).floatValue();
            lv = new CSS$LengthValue();
            lv.span = absolute;
        } catch (NumberFormatException nfe) {
            CSS$LengthUnit lu = new CSS$LengthUnit(value, CSS$LengthUnit.UNINITALIZED_LENGTH, 0);
            switch (lu.type) {
            case 0: 
                lv = new CSS$LengthValue();
                lv.span = (mayBeNegative) ? lu.value : Math.max(0, lu.value);
                lv.units = lu.units;
                break;
            
            case 1: 
                lv = new CSS$LengthValue();
                lv.span = Math.max(0, Math.min(1, lu.value));
                lv.percentage = true;
                break;
            
            default: 
                return null;
            
            }
        }
        lv.svalue = value;
        return lv;
    }
    
    Object parseHtmlValue(String value) {
        if (value.equals(HTML.NULL_ATTRIBUTE_VALUE)) {
            value = "1";
        }
        return parseCssValue(value);
    }
    
    Object fromStyleConstants(StyleConstants key, Object value) {
        CSS$LengthValue v = new CSS$LengthValue();
        v.svalue = value.toString();
        v.span = ((Float)(Float)value).floatValue();
        return v;
    }
    
    Object toStyleConstants(StyleConstants key, View v) {
        return new Float(getValue(false));
    }
    boolean percentage;
    float span;
    String units = null;
}
