package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$StringKeySet$1 implements Iterator {
    /*synthetic*/ final ProcessEnvironment$StringKeySet this$0;
    
    ProcessEnvironment$StringKeySet$1(/*synthetic*/ final ProcessEnvironment$StringKeySet this$0) {
        this.this$0 = this$0;
        
    }
    Iterator i = ProcessEnvironment.StringKeySet.access$800(this$0).iterator();
    
    public boolean hasNext() {
        return i.hasNext();
    }
    
    public String next() {
        return ((ProcessEnvironment$Variable)i.next()).toString();
    }
    
    public void remove() {
        i.remove();
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
