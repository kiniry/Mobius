package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedExceptionAction;

class FileSystemPreferences$8 implements PrivilegedExceptionAction {
    /*synthetic*/ final FileSystemPreferences this$0;
    
    FileSystemPreferences$8(/*synthetic*/ final FileSystemPreferences this$0) throws BackingStoreException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws BackingStoreException {
        try {
            if (!FileSystemPreferences.access$1400(this$0).exists() && !FileSystemPreferences.access$1400(this$0).mkdirs()) throw new BackingStoreException(FileSystemPreferences.access$1400(this$0) + " create failed.");
            FileOutputStream fos = new FileOutputStream(FileSystemPreferences.access$1800(this$0));
            XmlSupport.exportMap(fos, FileSystemPreferences.access$1100(this$0));
            fos.close();
            if (!FileSystemPreferences.access$1800(this$0).renameTo(FileSystemPreferences.access$1600(this$0))) throw new BackingStoreException("Can\'t rename " + FileSystemPreferences.access$1800(this$0) + " to " + FileSystemPreferences.access$1600(this$0));
        } catch (Exception e) {
            if (e instanceof BackingStoreException) throw (BackingStoreException)(BackingStoreException)e;
            throw new BackingStoreException(e);
        }
        return null;
    }
}
