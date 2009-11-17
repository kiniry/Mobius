package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedAction;

class FileSystemPreferences$3 implements PrivilegedAction {
    
    FileSystemPreferences$3() {
        
    }
    
    public Object run() {
        String systemPrefsDirName = (String)System.getProperty("java.util.prefs.systemRoot", "/etc/.java");
        FileSystemPreferences.access$602(new File(systemPrefsDirName, ".systemPrefs"));
        if (!FileSystemPreferences.access$600().exists()) {
            FileSystemPreferences.access$602(new File(System.getProperty("java.home"), ".systemPrefs"));
            if (!FileSystemPreferences.access$600().exists()) {
                if (FileSystemPreferences.access$600().mkdirs()) {
                    FileSystemPreferences.access$200().info("Created system preferences directory in java.home.");
                    try {
                        FileSystemPreferences.access$100(FileSystemPreferences.access$600().getCanonicalPath(), 493);
                    } catch (IOException e) {
                    }
                } else {
                    FileSystemPreferences.access$200().warning("Could not create system preferences directory. System preferences are unusable.");
                }
            }
        }
        FileSystemPreferences.access$702(FileSystemPreferences.access$600().canWrite());
        FileSystemPreferences.systemLockFile = new File(FileSystemPreferences.access$600(), ".system.lock");
        FileSystemPreferences.access$802(new File(FileSystemPreferences.access$600(), ".systemRootModFile"));
        if (!FileSystemPreferences.access$800().exists() && FileSystemPreferences.access$700()) try {
            FileSystemPreferences.access$800().createNewFile();
            int result = FileSystemPreferences.access$100(FileSystemPreferences.access$800().getCanonicalPath(), 420);
            if (result != 0) FileSystemPreferences.access$200().warning("Chmod failed on " + FileSystemPreferences.access$800().getCanonicalPath() + " Unix error code " + result);
        } catch (IOException e) {
            FileSystemPreferences.access$200().warning(e.toString());
        }
        FileSystemPreferences.access$902(FileSystemPreferences.access$800().lastModified());
        return null;
    }
}
