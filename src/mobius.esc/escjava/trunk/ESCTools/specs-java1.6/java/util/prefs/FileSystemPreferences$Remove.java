package java.util.prefs;

import java.util.*;
import java.io.*;

class FileSystemPreferences$Remove extends FileSystemPreferences$Change {
    /*synthetic*/ final FileSystemPreferences this$0;
    String key;
    
    FileSystemPreferences$Remove(/*synthetic*/ final FileSystemPreferences this$0, String key) {
        super(this.this$0 =this$0, null);
        this.key = key;
    }
    
    void replay() {
        FileSystemPreferences.access$1100(this$0).remove(key);
    }
}
