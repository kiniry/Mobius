package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$BorderStyle extends CSS$CssValue {
    
    CSS$BorderStyle() {
        
    }
    
    CSS$Value getValue() {
        return style;
    }
    
    Object parseCssValue(String value) {
        CSS$Value cssv = CSS.getValue(value);
        if (cssv != null) {
            if ((cssv == CSS$Value.INSET) || (cssv == CSS$Value.OUTSET) || (cssv == CSS$Value.NONE) || (cssv == CSS$Value.DOTTED) || (cssv == CSS$Value.DASHED) || (cssv == CSS$Value.SOLID) || (cssv == CSS$Value.DOUBLE) || (cssv == CSS$Value.GROOVE) || (cssv == CSS$Value.RIDGE)) {
                CSS$BorderStyle bs = new CSS$BorderStyle();
                bs.svalue = value;
                bs.style = cssv;
                return bs;
            }
        }
        return null;
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (style == null) {
            s.writeObject(null);
        } else {
            s.writeObject(style.toString());
        }
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        Object value = s.readObject();
        if (value != null) {
            style = CSS.getValue((String)(String)value);
        }
    }
    private transient CSS$Value style;
}
