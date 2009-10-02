package java.security;

import java.io.*;
import java.util.*;
import java.lang.ref.*;
import java.lang.reflect.*;

class Provider$UString {
    final String string;
    final String lowerString;
    
    Provider$UString(String s) {
        
        this.string = s;
        this.lowerString = s.toLowerCase(Locale.ENGLISH);
    }
    
    public int hashCode() {
        return lowerString.hashCode();
    }
    
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj instanceof Provider$UString == false) {
            return false;
        }
        Provider$UString other = (Provider$UString)(Provider$UString)obj;
        return lowerString.equals(other.lowerString);
    }
    
    public String toString() {
        return string;
    }
}
