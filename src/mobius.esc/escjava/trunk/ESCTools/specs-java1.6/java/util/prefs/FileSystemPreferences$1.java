package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedAction;

class FileSystemPreferences$1 implements PrivilegedAction {
    
    FileSystemPreferences$1() {
        
    }
    
    public Object run() {
        return System.getProperty("java.util.prefs.syncInterval", "30");
    }
}
