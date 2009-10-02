package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedExceptionAction;

class FileSystemPreferences$7 implements PrivilegedExceptionAction {
    /*synthetic*/ final FileSystemPreferences this$0;
    
    FileSystemPreferences$7(/*synthetic*/ final FileSystemPreferences this$0) throws BackingStoreException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws BackingStoreException {
        Map m = new TreeMap();
        long newLastSyncTime = 0;
        try {
            newLastSyncTime = FileSystemPreferences.access$1600(this$0).lastModified();
            FileInputStream fis = new FileInputStream(FileSystemPreferences.access$1600(this$0));
            XmlSupport.importMap(fis, m);
            fis.close();
        } catch (Exception e) {
            if (e instanceof InvalidPreferencesFormatException) {
                FileSystemPreferences.access$200().warning("Invalid preferences format in " + FileSystemPreferences.access$1600(this$0).getPath());
                FileSystemPreferences.access$1600(this$0).renameTo(new File(FileSystemPreferences.access$1600(this$0).getParentFile(), "IncorrectFormatPrefs.xml"));
                m = new TreeMap();
            } else if (e instanceof FileNotFoundException) {
                FileSystemPreferences.access$200().warning("Prefs file removed in background " + FileSystemPreferences.access$1600(this$0).getPath());
            } else {
                throw new BackingStoreException(e);
            }
        }
        FileSystemPreferences.access$1102(this$0, m);
        FileSystemPreferences.access$1702(this$0, newLastSyncTime);
        return null;
    }
}
