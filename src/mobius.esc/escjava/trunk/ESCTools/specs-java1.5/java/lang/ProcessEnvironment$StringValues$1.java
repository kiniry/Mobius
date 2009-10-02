package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$StringValues$1 implements Iterator {
    /*synthetic*/ final ProcessEnvironment$StringValues this$0;
    
    ProcessEnvironment$StringValues$1(/*synthetic*/ final ProcessEnvironment$StringValues this$0) {
        this.this$0 = this$0;
        
    }
    Iterator i = ProcessEnvironment.StringValues.access$700(this$0).iterator();
    
    public boolean hasNext() {
        return i.hasNext();
    }
    
    public String next() {
        return ((ProcessEnvironment$Value)i.next()).toString();
    }
    
    public void remove() {
        i.remove();
    }
    
    /*synthetic*/ public Object next() {
        return this.next();
    }
}
