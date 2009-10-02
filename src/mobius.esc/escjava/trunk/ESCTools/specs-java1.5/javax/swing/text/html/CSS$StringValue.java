package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$StringValue extends CSS$CssValue {
    
    CSS$StringValue() {
        
    }
    
    Object parseCssValue(String value) {
        CSS$StringValue sv = new CSS$StringValue();
        sv.svalue = value;
        return sv;
    }
    
    Object fromStyleConstants(StyleConstants key, Object value) {
        if (key == StyleConstants.Italic) {
            if (value.equals(Boolean.TRUE)) {
                return parseCssValue("italic");
            }
            return parseCssValue("");
        } else if (key == StyleConstants.Underline) {
            if (value.equals(Boolean.TRUE)) {
                return parseCssValue("underline");
            }
            return parseCssValue("");
        } else if (key == StyleConstants.Alignment) {
            int align = ((Integer)(Integer)value).intValue();
            String ta;
            switch (align) {
            case StyleConstants.ALIGN_LEFT: 
                ta = "left";
                break;
            
            case StyleConstants.ALIGN_RIGHT: 
                ta = "right";
                break;
            
            case StyleConstants.ALIGN_CENTER: 
                ta = "center";
                break;
            
            case StyleConstants.ALIGN_JUSTIFIED: 
                ta = "justify";
                break;
            
            default: 
                ta = "left";
            
            }
            return parseCssValue(ta);
        } else if (key == StyleConstants.StrikeThrough) {
            if (value.equals(Boolean.TRUE)) {
                return parseCssValue("line-through");
            }
            return parseCssValue("");
        } else if (key == StyleConstants.Superscript) {
            if (value.equals(Boolean.TRUE)) {
                return parseCssValue("super");
            }
            return parseCssValue("");
        } else if (key == StyleConstants.Subscript) {
            if (value.equals(Boolean.TRUE)) {
                return parseCssValue("sub");
            }
            return parseCssValue("");
        }
        return null;
    }
    
    Object toStyleConstants(StyleConstants key, View v) {
        if (key == StyleConstants.Italic) {
            if (svalue.indexOf("italic") >= 0) {
                return Boolean.TRUE;
            }
            return Boolean.FALSE;
        } else if (key == StyleConstants.Underline) {
            if (svalue.indexOf("underline") >= 0) {
                return Boolean.TRUE;
            }
            return Boolean.FALSE;
        } else if (key == StyleConstants.Alignment) {
            if (svalue.equals("right")) {
                return new Integer(StyleConstants.ALIGN_RIGHT);
            } else if (svalue.equals("center")) {
                return new Integer(StyleConstants.ALIGN_CENTER);
            } else if (svalue.equals("justify")) {
                return new Integer(StyleConstants.ALIGN_JUSTIFIED);
            }
            return new Integer(StyleConstants.ALIGN_LEFT);
        } else if (key == StyleConstants.StrikeThrough) {
            if (svalue.indexOf("line-through") >= 0) {
                return Boolean.TRUE;
            }
            return Boolean.FALSE;
        } else if (key == StyleConstants.Superscript) {
            if (svalue.indexOf("super") >= 0) {
                return Boolean.TRUE;
            }
            return Boolean.FALSE;
        } else if (key == StyleConstants.Subscript) {
            if (svalue.indexOf("sub") >= 0) {
                return Boolean.TRUE;
            }
            return Boolean.FALSE;
        }
        return null;
    }
    
    boolean isItalic() {
        return (svalue.indexOf("italic") != -1);
    }
    
    boolean isStrike() {
        return (svalue.indexOf("line-through") != -1);
    }
    
    boolean isUnderline() {
        return (svalue.indexOf("underline") != -1);
    }
    
    boolean isSub() {
        return (svalue.indexOf("sub") != -1);
    }
    
    boolean isSup() {
        return (svalue.indexOf("sup") != -1);
    }
}
