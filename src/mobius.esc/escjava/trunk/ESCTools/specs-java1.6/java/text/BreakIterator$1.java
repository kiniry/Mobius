package java.text;

import java.util.Locale;
import java.util.ResourceBundle;
import java.security.PrivilegedAction;

class BreakIterator$1 implements PrivilegedAction {
    /*synthetic*/ final Locale val$locale;
    /*synthetic*/ final String val$baseName;
    
    BreakIterator$1(/*synthetic*/ final String val$baseName, /*synthetic*/ final Locale val$locale) {
        this.val$baseName = val$baseName;
        this.val$locale = val$locale;
        
    }
    
    public Object run() {
        return ResourceBundle.getBundle(val$baseName, val$locale);
    }
}
