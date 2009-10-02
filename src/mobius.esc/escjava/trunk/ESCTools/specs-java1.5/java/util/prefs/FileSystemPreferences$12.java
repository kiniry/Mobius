package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedAction;

class FileSystemPreferences$12 implements PrivilegedAction {
    /*synthetic*/ final FileSystemPreferences this$0;
    /*synthetic*/ final Long val$newModTime;
    
    FileSystemPreferences$12(/*synthetic*/ final FileSystemPreferences this$0, /*synthetic*/ final Long val$newModTime) {
        this.this$0 = this$0;
        this.val$newModTime = val$newModTime;
        
    }
    
    public Object run() {
        if (this$0.isUserNode()) {
            FileSystemPreferences.access$502(val$newModTime.longValue() + 1000);
            FileSystemPreferences.access$400().setLastModified(FileSystemPreferences.access$500());
        } else {
            FileSystemPreferences.access$902(val$newModTime.longValue() + 1000);
            FileSystemPreferences.access$800().setLastModified(FileSystemPreferences.access$900());
        }
        return null;
    }
}
