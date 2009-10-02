package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedExceptionAction;

class FileSystemPreferences$10 implements PrivilegedExceptionAction {
    /*synthetic*/ final FileSystemPreferences this$0;
    
    FileSystemPreferences$10(/*synthetic*/ final FileSystemPreferences this$0) throws BackingStoreException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws BackingStoreException {
        if (this$0.changeLog.contains(this$0.nodeCreate)) {
            this$0.changeLog.remove(this$0.nodeCreate);
            this$0.nodeCreate = null;
            return null;
        }
        if (!FileSystemPreferences.access$1400(this$0).exists()) return null;
        FileSystemPreferences.access$1600(this$0).delete();
        FileSystemPreferences.access$1800(this$0).delete();
        File[] junk = FileSystemPreferences.access$1400(this$0).listFiles();
        if (junk.length != 0) {
            FileSystemPreferences.access$200().warning("Found extraneous files when removing node: " + Arrays.asList(junk));
            for (int i = 0; i < junk.length; i++) junk[i].delete();
        }
        if (!FileSystemPreferences.access$1400(this$0).delete()) throw new BackingStoreException("Couldn\'t delete dir: " + FileSystemPreferences.access$1400(this$0));
        return null;
    }
}
