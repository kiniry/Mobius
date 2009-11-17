package java.security;

import java.io.*;
import java.util.*;
import java.lang.ref.*;
import java.lang.reflect.*;

class Provider$ServiceKey {
    
    /*synthetic*/ Provider$ServiceKey(String x0, String x1, boolean x2, java.security.Provider$1 x3) {
        this(x0, x1, x2);
    }
    private final String type;
    private final String algorithm;
    private final String originalAlgorithm;
    
    private Provider$ServiceKey(String type, String algorithm, boolean intern) {
        
        this.type = type;
        this.originalAlgorithm = algorithm;
        algorithm = algorithm.toUpperCase(Locale.ENGLISH);
        this.algorithm = intern ? algorithm.intern() : algorithm;
    }
    
    public int hashCode() {
        return type.hashCode() + algorithm.hashCode();
    }
    
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj instanceof Provider$ServiceKey == false) {
            return false;
        }
        Provider$ServiceKey other = (Provider$ServiceKey)(Provider$ServiceKey)obj;
        return this.type.equals(other.type) && this.algorithm.equals(other.algorithm);
    }
    
    boolean matches(String type, String algorithm) {
        return (this.type == type) && (this.originalAlgorithm == algorithm);
    }
}
