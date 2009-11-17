package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$3 implements PrivilegedAction {
    /*synthetic*/ final LogManager this$0;
    /*synthetic*/ final String val$name;
    
    LogManager$3(/*synthetic*/ final LogManager this$0, /*synthetic*/ final String val$name) {
        this.this$0 = this$0;
        this.val$name = val$name;
        
    }
    
    public Object run() {
        String[] names = LogManager.access$600(this$0, val$name + ".handlers");
        for (int i = 0; i < names.length; i++) {
            String word = names[i];
            try {
                Class clz = ClassLoader.getSystemClassLoader().loadClass(word);
                Handler h = (Handler)(Handler)clz.newInstance();
                try {
                    String levs = this$0.getProperty(word + ".level");
                    if (levs != null) {
                        h.setLevel(Level.parse(levs));
                    }
                    boolean useParent = this$0.getBooleanProperty(val$name + ".useParentHandlers", true);
                    if (!useParent) {
                        this$0.getLogger(val$name).setUseParentHandlers(false);
                    }
                } catch (Exception ex) {
                    System.err.println("Can\'t set level for " + word);
                }
                this$0.getLogger(val$name).addHandler(h);
            } catch (Exception ex) {
                System.err.println("Can\'t load log handler \"" + word + "\"");
                System.err.println("" + ex);
                ex.printStackTrace();
            }
        }
        return null;
    }
}
