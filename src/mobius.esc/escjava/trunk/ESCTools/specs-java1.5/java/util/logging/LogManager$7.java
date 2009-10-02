package java.util.logging;

import java.io.*;
import java.util.*;
import java.security.*;

class LogManager$7 implements PrivilegedAction {
    /*synthetic*/ final LogManager this$0;
    
    LogManager$7(/*synthetic*/ final LogManager this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        String[] names = LogManager.access$600(this$0, "handlers");
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
                LogManager.access$100(this$0).addHandler(h);
            } catch (Exception ex) {
                System.err.println("Can\'t load log handler \"" + word + "\"");
                System.err.println("" + ex);
                ex.printStackTrace();
            }
        }
        return null;
    }
}
