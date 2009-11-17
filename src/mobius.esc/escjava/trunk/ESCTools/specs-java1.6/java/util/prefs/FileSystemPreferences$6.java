package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedAction;

class FileSystemPreferences$6 implements PrivilegedAction {
    /*synthetic*/ final FileSystemPreferences this$0;
    
    FileSystemPreferences$6(/*synthetic*/ final FileSystemPreferences this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        this$0.newNode = !FileSystemPreferences.access$1400(this$0).exists();
        return null;
    }
}
