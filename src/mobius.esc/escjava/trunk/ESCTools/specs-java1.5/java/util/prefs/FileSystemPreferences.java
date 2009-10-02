package java.util.prefs;

import java.util.*;
import java.io.*;
import java.util.logging.Logger;
import java.security.AccessController;
import java.security.PrivilegedActionException;

class FileSystemPreferences extends AbstractPreferences {
    
    /*synthetic*/ static void access$2300(FileSystemPreferences x0) throws BackingStoreException {
        x0.syncSpiPrivileged();
    }
    
    /*synthetic*/ static boolean access$2202(boolean x0) {
        return isSystemRootModified = x0;
    }
    
    /*synthetic*/ static boolean access$2102(boolean x0) {
        return isUserRootModified = x0;
    }
    
    /*synthetic*/ static String[] access$2000() {
        return EMPTY_STRING_ARRAY;
    }
    
    /*synthetic*/ static String access$1900(String x0) {
        return nodeName(x0);
    }
    
    /*synthetic*/ static File access$1800(FileSystemPreferences x0) {
        return x0.tmpFile;
    }
    
    /*synthetic*/ static long access$1702(FileSystemPreferences x0, long x1) {
        return x0.lastSyncTime = x1;
    }
    
    /*synthetic*/ static File access$1600(FileSystemPreferences x0) {
        return x0.prefsFile;
    }
    
    /*synthetic*/ static File access$1400(FileSystemPreferences x0) {
        return x0.dir;
    }
    
    /*synthetic*/ static Timer access$1300() {
        return syncTimer;
    }
    
    /*synthetic*/ static void access$1200() {
        syncWorld();
    }
    
    /*synthetic*/ static Map access$1102(FileSystemPreferences x0, Map x1) {
        return x0.prefsCache = x1;
    }
    
    /*synthetic*/ static Map access$1100(FileSystemPreferences x0) {
        return x0.prefsCache;
    }
    
    /*synthetic*/ static long access$902(long x0) {
        return systemRootModTime = x0;
    }
    
    /*synthetic*/ static long access$900() {
        return systemRootModTime;
    }
    
    /*synthetic*/ static File access$802(File x0) {
        return systemRootModFile = x0;
    }
    
    /*synthetic*/ static File access$800() {
        return systemRootModFile;
    }
    
    /*synthetic*/ static boolean access$702(boolean x0) {
        return isSystemRootWritable = x0;
    }
    
    /*synthetic*/ static boolean access$700() {
        return isSystemRootWritable;
    }
    
    /*synthetic*/ static File access$602(File x0) {
        return systemRootDir = x0;
    }
    
    /*synthetic*/ static File access$600() {
        return systemRootDir;
    }
    
    /*synthetic*/ static long access$502(long x0) {
        return userRootModTime = x0;
    }
    
    /*synthetic*/ static long access$500() {
        return userRootModTime;
    }
    
    /*synthetic*/ static File access$402(File x0) {
        return userRootModFile = x0;
    }
    
    /*synthetic*/ static File access$400() {
        return userRootModFile;
    }
    
    /*synthetic*/ static boolean access$302(boolean x0) {
        return isUserRootWritable = x0;
    }
    
    /*synthetic*/ static Logger access$200() {
        return getLogger();
    }
    
    /*synthetic*/ static int access$100(String x0, int x1) {
        return chmod(x0, x1);
    }
    
    /*synthetic*/ static File access$002(File x0) {
        return userRootDir = x0;
    }
    
    /*synthetic*/ static File access$000() {
        return userRootDir;
    }
    private static final int SYNC_INTERVAL = Math.max(1, Integer.parseInt((String)(String)AccessController.doPrivileged(new FileSystemPreferences$1())));
    
    private static Logger getLogger() {
        return Logger.getLogger("java.util.prefs");
    }
    private static File systemRootDir;
    private static boolean isSystemRootWritable;
    private static File userRootDir;
    private static boolean isUserRootWritable;
    static Preferences userRoot = null;
    
    static synchronized Preferences getUserRoot() {
        if (userRoot == null) {
            setupUserRoot();
            userRoot = new FileSystemPreferences(true);
        }
        return userRoot;
    }
    
    private static void setupUserRoot() {
        AccessController.doPrivileged(new FileSystemPreferences$2());
    }
    static Preferences systemRoot;
    
    static synchronized Preferences getSystemRoot() {
        if (systemRoot == null) {
            setupSystemRoot();
            systemRoot = new FileSystemPreferences(false);
        }
        return systemRoot;
    }
    
    private static void setupSystemRoot() {
        AccessController.doPrivileged(new FileSystemPreferences$3());
    }
    private static final int USER_READ_WRITE = 384;
    private static final int USER_RW_ALL_READ = 420;
    private static final int USER_RWX_ALL_RX = 493;
    private static final int USER_RWX = 448;
    static File userLockFile;
    static File systemLockFile;
    private static int userRootLockHandle = 0;
    private static int systemRootLockHandle = 0;
    private final File dir;
    private final File prefsFile;
    private final File tmpFile;
    private static File userRootModFile;
    private static boolean isUserRootModified = false;
    private static long userRootModTime;
    private static File systemRootModFile;
    private static boolean isSystemRootModified = false;
    private static long systemRootModTime;
    private Map prefsCache = null;
    private long lastSyncTime = 0;
    private static final int EAGAIN = 11;
    private static final int EACCES = 13;
    private static final int LOCK_HANDLE = 0;
    private static final int ERROR_CODE = 1;
    final List changeLog = new ArrayList();
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    FileSystemPreferences$NodeCreate nodeCreate = null;
    
    private void replayChanges() {
        for (int i = 0, n = changeLog.size(); i < n; i++) ((FileSystemPreferences$Change)(FileSystemPreferences$Change)changeLog.get(i)).replay();
    }
    private static Timer syncTimer = new Timer(true);
    static {
        syncTimer.schedule(new FileSystemPreferences$4(), SYNC_INTERVAL * 1000, SYNC_INTERVAL * 1000);
        AccessController.doPrivileged(new FileSystemPreferences$5());
    }
    
    private static void syncWorld() {
        Preferences userRt;
        Preferences systemRt;
        synchronized (FileSystemPreferences.class) {
            userRt = userRoot;
            systemRt = systemRoot;
        }
        try {
            if (userRt != null) userRt.flush();
        } catch (BackingStoreException e) {
            getLogger().warning("Couldn\'t flush user prefs: " + e);
        }
        try {
            if (systemRt != null) systemRt.flush();
        } catch (BackingStoreException e) {
            getLogger().warning("Couldn\'t flush system prefs: " + e);
        }
    }
    private final boolean isUserNode;
    
    private FileSystemPreferences(boolean user) {
        super(null, "");
        isUserNode = user;
        dir = (user ? userRootDir : systemRootDir);
        prefsFile = new File(dir, "prefs.xml");
        tmpFile = new File(dir, "prefs.tmp");
    }
    
    private FileSystemPreferences(FileSystemPreferences parent, String name) {
        super(parent, name);
        isUserNode = parent.isUserNode;
        dir = new File(parent.dir, dirName(name));
        prefsFile = new File(dir, "prefs.xml");
        tmpFile = new File(dir, "prefs.tmp");
        AccessController.doPrivileged(new FileSystemPreferences$6(this));
        if (newNode) {
            prefsCache = new TreeMap();
            nodeCreate = new FileSystemPreferences$NodeCreate(this, null);
            changeLog.add(nodeCreate);
        }
    }
    
    public boolean isUserNode() {
        return isUserNode;
    }
    
    protected void putSpi(String key, String value) {
        initCacheIfNecessary();
        changeLog.add(new FileSystemPreferences$Put(this, key, value));
        prefsCache.put(key, value);
    }
    
    protected String getSpi(String key) {
        initCacheIfNecessary();
        return (String)(String)prefsCache.get(key);
    }
    
    protected void removeSpi(String key) {
        initCacheIfNecessary();
        changeLog.add(new FileSystemPreferences$Remove(this, key));
        prefsCache.remove(key);
    }
    
    private void initCacheIfNecessary() {
        if (prefsCache != null) return;
        try {
            loadCache();
        } catch (Exception e) {
            prefsCache = new TreeMap();
        }
    }
    
    private void loadCache() throws BackingStoreException {
        try {
            AccessController.doPrivileged(new FileSystemPreferences$7(this));
        } catch (PrivilegedActionException e) {
            throw (BackingStoreException)(BackingStoreException)e.getException();
        }
    }
    
    private void writeBackCache() throws BackingStoreException {
        try {
            AccessController.doPrivileged(new FileSystemPreferences$8(this));
        } catch (PrivilegedActionException e) {
            throw (BackingStoreException)(BackingStoreException)e.getException();
        }
    }
    
    protected String[] keysSpi() {
        initCacheIfNecessary();
        return (String[])(String[])prefsCache.keySet().toArray(new String[prefsCache.size()]);
    }
    
    protected String[] childrenNamesSpi() {
        return (String[])(String[])AccessController.doPrivileged(new FileSystemPreferences$9(this));
    }
    private static final String[] EMPTY_STRING_ARRAY = new String[0];
    
    protected AbstractPreferences childSpi(String name) {
        return new FileSystemPreferences(this, name);
    }
    
    public void removeNode() throws BackingStoreException {
        synchronized (isUserNode() ? userLockFile : systemLockFile) {
            if (!lockFile(false)) throw (new BackingStoreException("Couldn\'t get file lock."));
            try {
                super.removeNode();
            } finally {
                unlockFile();
            }
        }
    }
    
    protected void removeNodeSpi() throws BackingStoreException {
        try {
            AccessController.doPrivileged(new FileSystemPreferences$10(this));
        } catch (PrivilegedActionException e) {
            throw (BackingStoreException)(BackingStoreException)e.getException();
        }
    }
    
    public synchronized void sync() throws BackingStoreException {
        boolean userNode = isUserNode();
        boolean shared;
        if (userNode) {
            shared = false;
        } else {
            shared = !isSystemRootWritable;
        }
        synchronized (isUserNode() ? userLockFile : systemLockFile) {
            if (!lockFile(shared)) throw (new BackingStoreException("Couldn\'t get file lock."));
            final Long newModTime = (Long)(Long)AccessController.doPrivileged(new FileSystemPreferences$11(this));
            try {
                super.sync();
                AccessController.doPrivileged(new FileSystemPreferences$12(this, newModTime));
            } finally {
                unlockFile();
            }
        }
    }
    
    protected void syncSpi() throws BackingStoreException {
        try {
            AccessController.doPrivileged(new FileSystemPreferences$13(this));
        } catch (PrivilegedActionException e) {
            throw (BackingStoreException)(BackingStoreException)e.getException();
        }
    }
    
    private void syncSpiPrivileged() throws BackingStoreException {
        if (isRemoved()) throw new IllegalStateException("Node has been removed");
        if (prefsCache == null) return;
        long lastModifiedTime;
        if (isUserNode() ? isUserRootModified : isSystemRootModified) {
            lastModifiedTime = prefsFile.lastModified();
            if (lastModifiedTime != lastSyncTime) {
                loadCache();
                replayChanges();
                lastSyncTime = lastModifiedTime;
            }
        } else if (lastSyncTime != 0 && !dir.exists()) {
            prefsCache = new TreeMap();
            replayChanges();
        }
        if (!changeLog.isEmpty()) {
            writeBackCache();
            lastModifiedTime = prefsFile.lastModified();
            if (lastSyncTime <= lastModifiedTime) {
                lastSyncTime = lastModifiedTime + 1000;
                prefsFile.setLastModified(lastSyncTime);
            }
            changeLog.clear();
        }
    }
    
    public void flush() throws BackingStoreException {
        if (isRemoved()) return;
        sync();
    }
    
    protected void flushSpi() throws BackingStoreException {
    }
    
    private static boolean isDirChar(char ch) {
        return ch > 31 && ch < 127 && ch != '/' && ch != '.' && ch != '_';
    }
    
    private static String dirName(String nodeName) {
        for (int i = 0, n = nodeName.length(); i < n; i++) if (!isDirChar(nodeName.charAt(i))) return "_" + Base64.byteArrayToAltBase64(byteArray(nodeName));
        return nodeName;
    }
    
    private static byte[] byteArray(String s) {
        int len = s.length();
        byte[] result = new byte[2 * len];
        for (int i = 0, j = 0; i < len; i++) {
            char c = s.charAt(i);
            result[j++] = (byte)(c >> 8);
            result[j++] = (byte)c;
        }
        return result;
    }
    
    private static String nodeName(String dirName) {
        if (dirName.charAt(0) != '_') return dirName;
        byte[] a = Base64.altBase64ToByteArray(dirName.substring(1));
        StringBuffer result = new StringBuffer(a.length / 2);
        for (int i = 0; i < a.length; ) {
            int highByte = a[i++] & 255;
            int lowByte = a[i++] & 255;
            result.append((char)((highByte << 8) | lowByte));
        }
        return result.toString();
    }
    
    private boolean lockFile(boolean shared) throws SecurityException {
        boolean usernode = isUserNode();
        int[] result;
        int errorCode = 0;
        File lockFile = (usernode ? userLockFile : systemLockFile);
        long sleepTime = INIT_SLEEP_TIME;
        for (int i = 0; i < MAX_ATTEMPTS; i++) {
            try {
                int perm = (usernode ? USER_READ_WRITE : USER_RW_ALL_READ);
                result = lockFile0(lockFile.getCanonicalPath(), perm, shared);
                errorCode = result[ERROR_CODE];
                if (result[LOCK_HANDLE] != 0) {
                    if (usernode) {
                        userRootLockHandle = result[LOCK_HANDLE];
                    } else {
                        systemRootLockHandle = result[LOCK_HANDLE];
                    }
                    return true;
                }
            } catch (IOException e) {
            }
            try {
                Thread.sleep(sleepTime);
            } catch (InterruptedException e) {
                checkLockFile0ErrorCode(errorCode);
                return false;
            }
            sleepTime *= 2;
        }
        checkLockFile0ErrorCode(errorCode);
        return false;
    }
    
    private void checkLockFile0ErrorCode(int errorCode) throws SecurityException {
        if (errorCode == EACCES) throw new SecurityException("Could not lock " + (isUserNode() ? "User prefs." : "System prefs.") + "Lock file access denied.");
        if (errorCode != EAGAIN) getLogger().warning("Could not lock " + (isUserNode() ? "User prefs. " : "System prefs.") + "Unix error code " + errorCode + ".");
    }
    
    private static native int[] lockFile0(String fileName, int permission, boolean shared);
    
    private static native int unlockFile0(int lockHandle);
    
    private static native int chmod(String fileName, int permission);
    private static int INIT_SLEEP_TIME = 50;
    private static int MAX_ATTEMPTS = 5;
    
    private void unlockFile() {
        int result;
        boolean usernode = isUserNode();
        File lockFile = (usernode ? userLockFile : systemLockFile);
        int lockHandle = (usernode ? userRootLockHandle : systemRootLockHandle);
        if (lockHandle == 0) {
            getLogger().warning("Unlock: zero lockHandle for " + (usernode ? "user" : "system") + " preferences.)");
            return;
        }
        result = unlockFile0(lockHandle);
        if (result != 0) {
            getLogger().warning("Could not drop file-lock on " + (isUserNode() ? "user" : "system") + " preferences." + "Unix error code " + result + ".");
            if (result == EACCES) throw new SecurityException("Could not unlock" + (isUserNode() ? "User prefs." : "System prefs.") + "Lock file access denied.");
        }
        if (isUserNode()) {
            userRootLockHandle = 0;
        } else {
            systemRootLockHandle = 0;
        }
    }
}
