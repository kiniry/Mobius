package java.util.prefs;

import java.util.*;
import java.io.*;

class FileSystemPreferences$Put extends FileSystemPreferences$Change {
    /*synthetic*/ final FileSystemPreferences this$0;
    String key;
    String value;
    
    FileSystemPreferences$Put(/*synthetic*/ final FileSystemPreferences this$0, String key, String value) {
        super(this.this$0 = this$0, null);
        this.key = key;
        this.value = value;
    }
    
    void replay() {
        FileSystemPreferences.access$1100(this$0).put(key, value);
    }
}
