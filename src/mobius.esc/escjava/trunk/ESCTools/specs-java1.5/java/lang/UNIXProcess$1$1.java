package java.lang;

import java.io.*;

class UNIXProcess$1$1 extends Thread {
    /*synthetic*/ final UNIXProcess$1 this$1;
    
    UNIXProcess$1$1(/*synthetic*/ final UNIXProcess$1 this$1, java.lang.String x0) {
        super(x0);
        this.this$1 = this$1;
    }
    
    public void run() {
        try {
            UNIXProcess.access$102(this$1.this$0, UNIXProcess.access$500(this$1.this$0, this$1.val$prog, this$1.val$argBlock, this$1.val$argc, this$1.val$envBlock, this$1.val$envc, this$1.val$dir, this$1.val$redirectErrorStream, UNIXProcess.access$200(this$1.this$0), UNIXProcess.access$300(this$1.this$0), UNIXProcess.access$400(this$1.this$0)));
        } catch (IOException e) {
            this$1.val$gate.setException(e);
            this$1.val$gate.exit();
            return;
        }
        java.security.AccessController.doPrivileged(new UNIXProcess$1$1$1(this));
        this$1.val$gate.exit();
        int res = UNIXProcess.access$900(this$1.this$0, UNIXProcess.access$100(this$1.this$0));
        synchronized (this$1.this$0) {
            UNIXProcess.access$1002(this$1.this$0, true);
            UNIXProcess.access$1102(this$1.this$0, res);
            this$1.this$0.notifyAll();
        }
    }
}
