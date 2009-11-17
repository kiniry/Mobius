package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedAction;

class FileSystemPreferences$11 implements PrivilegedAction {
    /*synthetic*/ final FileSystemPreferences this$0;
    
    FileSystemPreferences$11(/*synthetic*/ final FileSystemPreferences this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        long nmt;
        if (this$0.isUserNode()) {
            nmt = FileSystemPreferences.access$400().lastModified();
            FileSystemPreferences.access$2102(FileSystemPreferences.access$500() == nmt);
        } else {
            nmt = FileSystemPreferences.access$800().lastModified();
            FileSystemPreferences.access$2202(FileSystemPreferences.access$900() == nmt);
        }
        return new Long(nmt);
    }
}
