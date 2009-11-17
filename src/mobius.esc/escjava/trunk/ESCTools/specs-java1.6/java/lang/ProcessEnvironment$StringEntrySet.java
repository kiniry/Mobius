package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$StringEntrySet extends AbstractSet {
    
    /*synthetic*/ static Set access$500(ProcessEnvironment$StringEntrySet x0) {
        return x0.s;
    }
    private final Set s;
    
    public ProcessEnvironment$StringEntrySet(Set s) {
        
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
        return new ProcessEnvironment$StringEntrySet$1(this);
    }
    
    private static Map$Entry vvEntry(final Object o) {
        if (o instanceof ProcessEnvironment$StringEntry) return ProcessEnvironment.StringEntry.access$600(((ProcessEnvironment$StringEntry)(ProcessEnvironment$StringEntry)o));
        return new ProcessEnvironment$StringEntrySet$2(o);
    }
    
    public boolean contains(Object o) {
        return s.contains(vvEntry(o));
    }
    
    public boolean remove(Object o) {
        return s.remove(vvEntry(o));
    }
    
    public boolean equals(Object o) {
        return o instanceof ProcessEnvironment$StringEntrySet && s.equals(((ProcessEnvironment$StringEntrySet)(ProcessEnvironment$StringEntrySet)o).s);
    }
    
    public int hashCode() {
        return s.hashCode();
    }
}
