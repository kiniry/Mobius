package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$Value extends ProcessEnvironment$ExternalData implements Comparable {
    
    protected ProcessEnvironment$Value(String str, byte[] bytes) {
        super(str, bytes);
    }
    
    public static ProcessEnvironment$Value valueOfQueryOnly(Object str) {
        return valueOfQueryOnly((String)(String)str);
    }
    
    public static ProcessEnvironment$Value valueOfQueryOnly(String str) {
        return new ProcessEnvironment$Value(str, str.getBytes());
    }
    
    public static ProcessEnvironment$Value valueOf(String str) {
        ProcessEnvironment.access$400(str);
        return valueOfQueryOnly(str);
    }
    
    public static ProcessEnvironment$Value valueOf(byte[] bytes) {
        return new ProcessEnvironment$Value(new String(bytes), bytes);
    }
    
    public int compareTo(ProcessEnvironment$Value value) {
        return ProcessEnvironment.access$300(getBytes(), value.getBytes());
    }
    
    public boolean equals(Object o) {
        return o instanceof ProcessEnvironment$Value && super.equals(o);
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((ProcessEnvironment$Value)x0);
    }
}
