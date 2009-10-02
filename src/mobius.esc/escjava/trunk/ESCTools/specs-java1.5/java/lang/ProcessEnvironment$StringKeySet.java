package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$StringKeySet extends AbstractSet {
    
    /*synthetic*/ static Set access$800(ProcessEnvironment$StringKeySet x0) {
        return x0.s;
    }
    private final Set s;
    
    public ProcessEnvironment$StringKeySet(Set s) {
        
        this.s = s;
    }
    
    public int size() {
        return s.size();
    }
    
    public boolean isEmpty() {
        return s.isEmpty();
    }
    
    public void clear() {
        s.clear();
    }
    
    public Iterator iterator() {
        return new ProcessEnvironment$StringKeySet$1(this);
    }
    
    public boolean contains(Object o) {
        return s.contains(ProcessEnvironment$Variable.valueOfQueryOnly(o));
    }
    
    public boolean remove(Object o) {
        return s.remove(ProcessEnvironment$Variable.valueOfQueryOnly(o));
    }
}
