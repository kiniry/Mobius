package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

class CSS$CssValueMapper extends CSS$CssValue {
    
    CSS$CssValueMapper() {
        
    }
    
    Object parseCssValue(String value) {
        Object retValue = CSS.access$400().get(value);
        if (retValue == null) {
            retValue = CSS.access$400().get(value.toLowerCase());
        }
        return retValue;
    }
    
    Object parseHtmlValue(String value) {
        Object retValue = CSS.access$500().get(value);
        if (retValue == null) {
            retValue = CSS.access$500().get(value.toLowerCase());
        }
        return retValue;
    }
}
