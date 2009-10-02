package java.util;

import java.util.regex.*;
import java.io.*;
import java.math.*;
import java.nio.*;
import java.nio.channels.*;
import java.nio.charset.*;
import java.text.*;
import sun.misc.LRUCache;

class Scanner$1 extends LRUCache {
    /*synthetic*/ final Scanner this$0;
    
    Scanner$1(/*synthetic*/ final Scanner this$0, int x0) {
        super( this.this$0 = x0);
    }
    
    protected Pattern create(String s) {
        return Pattern.compile(s);
    }
    
    protected boolean hasName(Pattern p, String s) {
        return p.pattern().equals(s);
    }
    
    /*synthetic*/ protected boolean hasName(Object x0, Object x1) {
        return this.hasName((Pattern)x0, (String)x1);
    }
    
    /*synthetic*/ protected Object create(Object x0) {
        return this.create((String)x0);
    }
}
