package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedAction;

class AbstractPreferences$1 implements PrivilegedAction {
    /*synthetic*/ final AbstractPreferences this$0;
    
    AbstractPreferences$1(/*synthetic*/ final AbstractPreferences this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        return new Boolean(AbstractPreferences.access$000(this$0) == Preferences.userRoot());
    }
}
