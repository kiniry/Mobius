package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$4 implements PrivilegedAction {
    /*synthetic*/ final LogManager this$0;
    /*synthetic*/ final String val$nname;
    
    LogManager$4(/*synthetic*/ final LogManager this$0, /*synthetic*/ final String val$nname) {
        this.this$0 = this$0;
        this.val$nname = val$nname;
        
    }
    
    public Object run() {
        String[] names = LogManager.access$600(this$0, val$nname + ".handlers");
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
                } catch (Exception ex) {
                    System.err.println("Can\'t set level for " + word);
                }
                if (this$0.getLogger(val$nname) == null) {
                    Logger nplogger = this$0.demandLogger(val$nname);
                    this$0.addLogger(nplogger);
                }
                boolean useParent = this$0.getBooleanProperty(val$nname + ".useParentHandlers", true);
                if (!useParent) {
                    this$0.getLogger(val$nname).setUseParentHandlers(false);
                }
            } catch (Exception ex) {
                System.err.println("Can\'t load log handler \"" + word + "\"");
                System.err.println("" + ex);
                ex.printStackTrace();
            }
        }
        return null;
    }
}
