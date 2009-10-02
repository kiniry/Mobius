package java.text;

import java.io.BufferedInputStream;
import java.security.PrivilegedExceptionAction;

class RuleBasedBreakIterator$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final RuleBasedBreakIterator this$0;
    /*synthetic*/ final String val$datafile;
    
    RuleBasedBreakIterator$1(/*synthetic*/ final RuleBasedBreakIterator this$0, /*synthetic*/ final String val$datafile) {
        this.this$0 = this$0;
        this.val$datafile = val$datafile;
        
    }
    
    public Object run() throws Exception {
        return new BufferedInputStream(getClass().getResourceAsStream("/sun/text/resources/" + val$datafile));
    }
}
