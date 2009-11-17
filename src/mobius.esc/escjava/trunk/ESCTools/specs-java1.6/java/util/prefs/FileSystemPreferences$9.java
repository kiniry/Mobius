package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedAction;

class FileSystemPreferences$9 implements PrivilegedAction {
    /*synthetic*/ final FileSystemPreferences this$0;
    
    FileSystemPreferences$9(/*synthetic*/ final FileSystemPreferences this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        List result = new ArrayList();
        File[] dirContents = FileSystemPreferences.access$1400(this$0).listFiles();
        if (dirContents != null) {
            for (int i = 0; i < dirContents.length; i++) if (dirContents[i].isDirectory()) result.add(FileSystemPreferences.access$1900(dirContents[i].getName()));
        }
        return result.toArray(FileSystemPreferences.access$2000());
    }
}
