package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$Variable extends ProcessEnvironment$ExternalData implements Comparable {
    
    protected ProcessEnvironment$Variable(String str, byte[] bytes) {
        super(str, bytes);
    }
    
    public static ProcessEnvironment$Variable valueOfQueryOnly(Object str) {
        return valueOfQueryOnly((String)(String)str);
    }
    
    public static ProcessEnvironment$Variable valueOfQueryOnly(String str) {
        return new ProcessEnvironment$Variable(str, str.getBytes());
    }
    
    public static ProcessEnvironment$Variable valueOf(String str) {
        ProcessEnvironment.access$200(str);
        return valueOfQueryOnly(str);
    }
    
    public static ProcessEnvironment$Variable valueOf(byte[] bytes) {
        return new ProcessEnvironment$Variable(new String(bytes), bytes);
    }
    
    public int compareTo(ProcessEnvironment$Variable variable) {
        return ProcessEnvironment.access$300(getBytes(), variable.getBytes());
    }
    
    public boolean equals(Object o) {
        return o instanceof ProcessEnvironment$Variable && super.equals(o);
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((ProcessEnvironment$Variable)x0);
    }
}
