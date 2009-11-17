package java.lang;

import java.io.*;

class UNIXProcess$1$1$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final UNIXProcess$1$1 this$2;
    
    UNIXProcess$1$1$1(/*synthetic*/ final UNIXProcess$1$1 this$2) {
        this.this$2 = this$2;
        
    }
    
    public Object run() {
        UNIXProcess.access$602(this$2.this$1.this$0, new BufferedOutputStream(new FileOutputStream(UNIXProcess.access$200(this$2.this$1.this$0))));
        UNIXProcess.access$702(this$2.this$1.this$0, new BufferedInputStream(new FileInputStream(UNIXProcess.access$300(this$2.this$1.this$0))));
        UNIXProcess.access$802(this$2.this$1.this$0, new FileInputStream(UNIXProcess.access$400(this$2.this$1.this$0)));
        return null;
    }
}
