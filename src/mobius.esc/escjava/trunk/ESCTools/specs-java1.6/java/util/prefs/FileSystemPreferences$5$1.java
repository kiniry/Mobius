package java.util.prefs;

import java.util.*;
import java.io.*;

class FileSystemPreferences$5$1 extends Thread {
    /*synthetic*/ final FileSystemPreferences$5 this$0;
    
    FileSystemPreferences$5$1(/*synthetic*/ final FileSystemPreferences$5 this$0) {
        this.this$0 = this$0;
        
    }
    
    public void run() {
        FileSystemPreferences.access$1300().cancel();
        FileSystemPreferences.access$1200();
    }
}
