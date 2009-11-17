package java.lang;

import java.io.*;
import java.util.*;

abstract class ProcessEnvironment$ExternalData {
    protected final String str;
    protected final byte[] bytes;
    
    protected ProcessEnvironment$ExternalData(String str, byte[] bytes) {
        
        this.str = str;
        this.bytes = bytes;
    }
    
    public byte[] getBytes() {
        return bytes;
    }
    
    public String toString() {
        return str;
    }
    
    public boolean equals(Object o) {
        return o instanceof ProcessEnvironment$ExternalData && ProcessEnvironment.access$000(getBytes(), ((ProcessEnvironment$ExternalData)(ProcessEnvironment$ExternalData)o).getBytes());
    }
    
    public int hashCode() {
        return ProcessEnvironment.access$100(getBytes());
    }
}
