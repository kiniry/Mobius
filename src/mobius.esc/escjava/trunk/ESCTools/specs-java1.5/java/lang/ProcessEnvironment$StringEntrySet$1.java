package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$StringEntrySet$1 implements Iterator {
    /*synthetic*/ final ProcessEnvironment$StringEntrySet this$0;
    
    ProcessEnvironment$StringEntrySet$1(/*synthetic*/ final ProcessEnvironment$StringEntrySet this$0) {
        this.this$0 = this$0;
        
    }
    Iterator i = ProcessEnvironment.StringEntrySet.access$500(this$0).iterator();
    
    public boolean hasNext() {
        return i.hasNext();
    }
    
    public Map$Entry next() {
        return new ProcessEnvironment$StringEntry((Map$Entry)i.next());
    }
    
    public void remove() {
        i.remove();
    }
    
    /*synthetic public Object next() {
        return this.next();
    } */
}
