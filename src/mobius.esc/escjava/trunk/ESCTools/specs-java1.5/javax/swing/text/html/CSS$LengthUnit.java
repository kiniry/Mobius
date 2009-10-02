package javax.swing.text.html;

import java.awt.Toolkit;
import java.awt.HeadlessException;
import java.io.*;
import java.util.Hashtable;
import javax.swing.text.*;

class CSS$LengthUnit implements Serializable {
    static Hashtable lengthMapping = new Hashtable(6);
    static Hashtable w3cLengthMapping = new Hashtable(6);
    static {
        lengthMapping.put("pt", new Float(1.0F));
        lengthMapping.put("px", new Float(1.3F));
        lengthMapping.put("mm", new Float(2.83464F));
        lengthMapping.put("cm", new Float(28.3464F));
        lengthMapping.put("pc", new Float(12.0F));
        lengthMapping.put("in", new Float(72.0F));
        int res = 72;
        try {
            res = Toolkit.getDefaultToolkit().getScreenResolution();
        } catch (HeadlessException e) {
        }
        w3cLengthMapping.put("pt", new Float(res / 72.0F));
        w3cLengthMapping.put("px", new Float(1.0F));
        w3cLengthMapping.put("mm", new Float(res / 25.4F));
        w3cLengthMapping.put("cm", new Float(res / 2.54F));
        w3cLengthMapping.put("pc", new Float(res / 6.0F));
        w3cLengthMapping.put("in", new Float(res));
    }
    
    CSS$LengthUnit(String value, short defaultType, float defaultValue) {
        
        parse(value, defaultType, defaultValue);
    }
    
    void parse(String value, short defaultType, float defaultValue) {
        type = defaultType;
        this.value = defaultValue;
        int length = value.length();
        if (length > 0 && value.charAt(length - 1) == '%') {
            try {
                this.value = Float.valueOf(value.substring(0, length - 1)).floatValue() / 100.0F;
                type = 1;
            } catch (NumberFormatException nfe) {
            }
        }
        if (length >= 2) {
            units = value.substring(length - 2, length);
            Float scale = (Float)(Float)lengthMapping.get(units);
            if (scale != null) {
                try {
                    this.value = Float.valueOf(value.substring(0, length - 2)).floatValue();
                    type = 0;
                } catch (NumberFormatException nfe) {
                }
            } else if (units.equals("em") || units.equals("ex")) {
                try {
                    this.value = Float.valueOf(value.substring(0, length - 2)).floatValue();
                    type = 3;
                } catch (NumberFormatException nfe) {
                }
            } else if (value.equals("larger")) {
                this.value = 2.0F;
                type = 2;
            } else if (value.equals("smaller")) {
                this.value = -2;
                type = 2;
            } else {
                try {
                    this.value = Float.valueOf(value).floatValue();
                    type = 0;
                } catch (NumberFormatException nfe) {
                }
            }
        } else if (length > 0) {
            try {
                this.value = Float.valueOf(value).floatValue();
                type = 0;
            } catch (NumberFormatException nfe) {
            }
        }
    }
    
    float getValue(boolean w3cLengthUnits) {
        Hashtable mapping = (w3cLengthUnits) ? w3cLengthMapping : lengthMapping;
        float scale = 1;
        if (units != null) {
            Float scaleFloat = (Float)(Float)mapping.get(units);
            if (scaleFloat != null) {
                scale = scaleFloat.floatValue();
            }
        }
        return this.value * scale;
    }
    
    static float getValue(float value, String units, Boolean w3cLengthUnits) {
        Hashtable mapping = (w3cLengthUnits).booleanValue() ? w3cLengthMapping : lengthMapping;
        float scale = 1;
        if (units != null) {
            Float scaleFloat = (Float)(Float)mapping.get(units);
            if (scaleFloat != null) {
                scale = scaleFloat.floatValue();
            }
        }
        return value * scale;
    }
    
    public String toString() {
        return type + " " + value;
    }
    short type;
    float value;
    String units = null;
    static final short UNINITALIZED_LENGTH = (short)10;
}
