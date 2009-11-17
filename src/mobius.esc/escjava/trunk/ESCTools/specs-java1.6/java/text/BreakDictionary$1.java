package java.text;

import java.io.*;
import java.security.PrivilegedExceptionAction;

class BreakDictionary$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final BreakDictionary this$0;
    /*synthetic*/ final String val$dictionaryName;
    
    BreakDictionary$1(/*synthetic*/ final BreakDictionary this$0, /*synthetic*/ final String val$dictionaryName) {
        this.this$0 = this$0;
        this.val$dictionaryName = val$dictionaryName;
        
    }
    
    public Object run() throws Exception {
        return new BufferedInputStream(getClass().getResourceAsStream("/sun/text/resources/" + val$dictionaryName));
    }
}
