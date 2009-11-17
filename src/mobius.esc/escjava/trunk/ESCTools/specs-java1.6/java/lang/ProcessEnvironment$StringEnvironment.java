package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$StringEnvironment extends AbstractMap {
    private Map m;
    
    private static String toString(ProcessEnvironment$Value v) {
        return v == null ? null : v.toString();
    }
    
    public ProcessEnvironment$StringEnvironment(Map m) {
        
        this.m = m;
    }
    
    public int size() {
        return m.size();
    }
    
    public boolean isEmpty() {
        return m.isEmpty();
    }
    
    public void clear() {
        m.clear();
    }
    
    public boolean containsKey(Object key) {
        return m.containsKey(ProcessEnvironment$Variable.valueOfQueryOnly(key));
    }
    
    public boolean containsValue(Object value) {
        return m.containsValue(ProcessEnvironment$Value.valueOfQueryOnly(value));
    }
    
    public String get(Object key) {
        return toString((ProcessEnvironment$Value)m.get(ProcessEnvironment$Variable.valueOfQueryOnly(key)));
    }
    
    public String put(String key, String value) {
        return toString((ProcessEnvironment$Value)m.put(ProcessEnvironment$Variable.valueOf(key), ProcessEnvironment$Value.valueOf(value)));
    }
    
    public String remove(Object key) {
        return toString((ProcessEnvironment$Value)m.remove(ProcessEnvironment$Variable.valueOfQueryOnly(key)));
    }
    
    public Set keySet() {
        return new ProcessEnvironment$StringKeySet(m.keySet());
    }
    
    public Set entrySet() {
        return new ProcessEnvironment$StringEntrySet(m.entrySet());
    }
    
    public Collection values() {
        return new ProcessEnvironment$StringValues(m.values());
    }
    
    public byte[] toEnvironmentBlock(int[] envc) {
        int count = m.size() * 2;
        for (Iterator i$ = m.entrySet().iterator(); i$.hasNext(); ) {
            Map$Entry entry = (Map$Entry)i$.next();
            {
                count += ((ProcessEnvironment$Variable)entry.getKey()).getBytes().length;
                count += ((ProcessEnvironment$Value)entry.getValue()).getBytes().length;
            }
        }
        byte[] block = new byte[count];
        int i = 0;
        for (Iterator i$ = m.entrySet().iterator(); i$.hasNext(); ) {
            Map$Entry entry = (Map$Entry)i$.next();
            {
                byte[] key = ((ProcessEnvironment$Variable)entry.getKey()).getBytes();
                byte[] value = ((ProcessEnvironment$Value)entry.getValue()).getBytes();
                System.arraycopy(key, 0, block, i, key.length);
                i += key.length;
                block[i++] = (byte)'=';
                System.arraycopy(value, 0, block, i, value.length);
                i += value.length + 1;
            }
        }
        envc[0] = m.size();
        return block;
    }
    
    /*synthetic public Object remove(Object x0) {
        return this.remove(x0);
    } */
    
    /*synthetic public Object put(Object x0, Object x1) {
        return this.put((String)x0, (String)x1);
    }*/
    
    /*synthetic public Object get(Object x0) {
        return this.get(x0);
    }*/
}
