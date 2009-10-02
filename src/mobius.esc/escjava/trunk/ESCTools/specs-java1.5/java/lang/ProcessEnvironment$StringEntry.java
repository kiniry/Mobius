package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$StringEntry implements Map$Entry {
    
    /*synthetic*/ static Map$Entry access$600(ProcessEnvironment$StringEntry x0) {
        return x0.e;
    }
    private final Map$Entry e;
    
    public ProcessEnvironment$StringEntry(Map$Entry e) {
        
        this.e = e;
    }
    
    public String getKey() {
        return ((ProcessEnvironment$Variable)e.getKey()).toString();
    }
    
    public String getValue() {
        return ((ProcessEnvironment$Value)e.getValue()).toString();
    }
    
    public String setValue(String newValue) {
        return ((ProcessEnvironment$Value)e.setValue(ProcessEnvironment$Value.valueOf(newValue))).toString();
    }
    
    public String toString() {
        return getKey() + "=" + getValue();
    }
    
    public boolean equals(Object o) {
        return o instanceof ProcessEnvironment$StringEntry && e.equals(((ProcessEnvironment$StringEntry)(ProcessEnvironment$StringEntry)o).e);
    }
    
    public int hashCode() {
        return e.hashCode();
    }
    
    /*synthetic*/ public Object setValue(Object x0) {
        return this.setValue((String)x0);
    }
    
    /*synthetic*/ public Object getValue() {
        return this.getValue();
    }
    
    /*synthetic*/ public Object getKey() {
        return this.getKey();
    }
}
