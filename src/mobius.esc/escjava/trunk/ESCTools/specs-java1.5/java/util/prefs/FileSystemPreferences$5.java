package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedAction;

class FileSystemPreferences$5 implements PrivilegedAction {
    
    FileSystemPreferences$5() {
        
    }
    
    public Object run() {
        Runtime.getRuntime().addShutdownHook(new FileSystemPreferences$5$1(this));
        return null;
    }
}
