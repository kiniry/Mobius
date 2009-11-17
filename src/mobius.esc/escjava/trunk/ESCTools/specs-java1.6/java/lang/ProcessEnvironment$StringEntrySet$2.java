package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$StringEntrySet$2 implements Map$Entry {
    /*synthetic*/ final Object val$o;
    
    ProcessEnvironment$StringEntrySet$2(/*synthetic*/ final Object val$o) {
        this.val$o = val$o;
        
    }
    
    public ProcessEnvironment$Variable getKey() {
        return ProcessEnvironment$Variable.valueOfQueryOnly(((Map$Entry)(Map$Entry)val$o).getKey());
    }
    
    public ProcessEnvironment$Value getValue() {
        return ProcessEnvironment$Value.valueOfQueryOnly(((Map$Entry)(Map$Entry)val$o).getValue());
    }
    
    public ProcessEnvironment$Value setValue(ProcessEnvironment$Value value) {
        throw new UnsupportedOperationException();
    }
    
    /*synthetic public Object setValue(Object x0) {
        return this.setValue((ProcessEnvironment$Value)x0);
    } */

    /*synthetic public Object getValue() {
        return this.getValue();
    } */
    
    /*synthetic public Object getKey() {
        return this.getKey();
    } */
}
