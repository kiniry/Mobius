package java.lang;

import java.io.*;

class UNIXProcess$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final UNIXProcess this$0;
    /*synthetic*/ final UNIXProcess$Gate val$gate;
    /*synthetic*/ final boolean val$redirectErrorStream;
    /*synthetic*/ final byte[] val$dir;
    /*synthetic*/ final int val$envc;
    /*synthetic*/ final byte[] val$envBlock;
    /*synthetic*/ final int val$argc;
    /*synthetic*/ final byte[] val$argBlock;
    /*synthetic*/ final byte[] val$prog;
    
    UNIXProcess$1(/*synthetic*/ final UNIXProcess this$0, /*synthetic*/ final byte[] val$prog, /*synthetic*/ final byte[] val$argBlock, /*synthetic*/ final int val$argc, /*synthetic*/ final byte[] val$envBlock, /*synthetic*/ final int val$envc, /*synthetic*/ final byte[] val$dir, /*synthetic*/ final boolean val$redirectErrorStream, /*synthetic*/ final UNIXProcess$Gate val$gate) {
        this.this$0 = this$0;
        this.val$prog = val$prog;
        this.val$argBlock = val$argBlock;
        this.val$argc = val$argc;
        this.val$envBlock = val$envBlock;
        this.val$envc = val$envc;
        this.val$dir = val$dir;
        this.val$redirectErrorStream = val$redirectErrorStream;
        this.val$gate = val$gate;
        
    }
    
    public Object run() {
        Thread t = new UNIXProcess$1$1(this, "process reaper");
        t.setDaemon(true);
        t.start();
        return null;
    }
}
