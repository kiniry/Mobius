package java.util;

import java.io.IOException;
import java.util.Locale;

class Formatter$FixedString implements Formatter$FormatString {
    /*synthetic*/ final Formatter this$0;
    private String s;
    
    Formatter$FixedString(/*synthetic*/ final Formatter this$0, String s) {
        this.this$0 = this$0;
        
        this.s = s;
    }
    
    public int index() {
        return -2;
    }
    
    public void print(Object arg, Locale l) throws IOException {
        Formatter.access$000(this$0).append(s);
    }
    
    public String toString() {
        return s;
    }
}
