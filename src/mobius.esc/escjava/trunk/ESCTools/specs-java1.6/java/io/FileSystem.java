package java.io;

abstract class FileSystem {
    
    FileSystem() {
        
    }
    
    public static native FileSystem getFileSystem();
    
    public abstract char getSeparator();
    
    public abstract char getPathSeparator();
    
    public abstract String normalize(String path);
    
    public abstract int prefixLength(String path);
    
    public abstract String resolve(String parent, String child);
    
    public abstract String getDefaultParent();
    
    public abstract String fromURIPath(String path);
    
    public abstract boolean isAbsolute(File f);
    
    public abstract String resolve(File f);
    
    public abstract String canonicalize(String path) throws IOException;
    public static final int BA_EXISTS = 1;
    public static final int BA_REGULAR = 2;
    public static final int BA_DIRECTORY = 4;
    public static final int BA_HIDDEN = 8;
    
    public abstract int getBooleanAttributes(File f);
    
    public abstract boolean checkAccess(File f, boolean write);
    
    public abstract long getLastModifiedTime(File f);
    
    public abstract long getLength(File f);
    
    public abstract boolean createFileExclusively(String pathname) throws IOException;
    
    public abstract boolean delete(File f);
    
    public abstract boolean deleteOnExit(File f);
    
    public abstract String[] list(File f);
    
    public abstract boolean createDirectory(File f);
    
    public abstract boolean rename(File f1, File f2);
    
    public abstract boolean setLastModifiedTime(File f, long time);
    
    public abstract boolean setReadOnly(File f);
    
    public abstract File[] listRoots();
    
    public abstract int compare(File f1, File f2);
    
    public abstract int hashCode(File f);
    static boolean useCanonCaches = true;
    static boolean useCanonPrefixCache = true;
    
    private static boolean getBooleanProperty(String prop, boolean defaultVal) {
        String val = System.getProperty(prop);
        if (val == null) return defaultVal;
        if (val.equalsIgnoreCase("true")) {
            return true;
        } else {
            return false;
        }
    }
    static {
        useCanonCaches = getBooleanProperty("sun.io.useCanonCaches", useCanonCaches);
        useCanonPrefixCache = getBooleanProperty("sun.io.useCanonPrefixCache", useCanonPrefixCache);
    }
}
