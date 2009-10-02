package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.PrivilegedAction;

class FileSystemPreferences$2 implements PrivilegedAction {
    
    FileSystemPreferences$2() {
        
    }
    
    public Object run() {
        FileSystemPreferences.access$002(new File(System.getProperty("java.util.prefs.userRoot", System.getProperty("user.home")), ".java/.userPrefs"));
        if (!FileSystemPreferences.access$000().exists()) {
            if (FileSystemPreferences.access$000().mkdirs()) {
                try {
                    FileSystemPreferences.access$100(FileSystemPreferences.access$000().getCanonicalPath(), 448);
                } catch (IOException e) {
                    FileSystemPreferences.access$200().warning("Could not change permissions on userRoot directory. ");
                }
                FileSystemPreferences.access$200().info("Created user preferences directory.");
            } else FileSystemPreferences.access$200().warning("Couldn\'t create user preferences directory. User preferences are unusable.");
        }
        FileSystemPreferences.access$302(FileSystemPreferences.access$000().canWrite());
        String USER_NAME = System.getProperty("user.name");
        FileSystemPreferences.userLockFile = new File(FileSystemPreferences.access$000(), ".user.lock." + USER_NAME);
        FileSystemPreferences.access$402(new File(FileSystemPreferences.access$000(), ".userRootModFile." + USER_NAME));
        if (!FileSystemPreferences.access$400().exists()) try {
            FileSystemPreferences.access$400().createNewFile();
            int result = FileSystemPreferences.access$100(FileSystemPreferences.access$400().getCanonicalPath(), 384);
            if (result != 0) FileSystemPreferences.access$200().warning("Problem creating userRoot " + "mod file. Chmod failed on " + FileSystemPreferences.access$400().getCanonicalPath() + " Unix error code " + result);
        } catch (IOException e) {
            FileSystemPreferences.access$200().warning(e.toString());
        }
        FileSystemPreferences.access$502(FileSystemPreferences.access$400().lastModified());
        return null;
    }
}
