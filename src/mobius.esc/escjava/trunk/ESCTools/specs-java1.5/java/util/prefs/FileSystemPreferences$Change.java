package java.util.prefs;

import java.util.*;
import java.io.*;

abstract class FileSystemPreferences$Change {
    
    /*synthetic*/ FileSystemPreferences$Change(FileSystemPreferences x0, java.util.prefs.FileSystemPreferences$1 x1) {
        this(x0);
    }
    /*synthetic*/ final FileSystemPreferences this$0;
    
    private FileSystemPreferences$Change(/*synthetic*/ final FileSystemPreferences this$0) {
        this.this$0 = this$0;
        
    }
    
    abstract void replay();
}
