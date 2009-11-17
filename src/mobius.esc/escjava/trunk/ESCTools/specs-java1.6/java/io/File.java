package java.io;

import java.net.URI;
import java.net.URL;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.security.AccessControlException;

public class File implements Serializable, Comparable {
    
    /*synthetic*/ static FileSystem access$000() {
        return fs;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !File.class.desiredAssertionStatus();
    private static FileSystem fs = FileSystem.getFileSystem();
    private String path;
    private transient int prefixLength;
    
    int getPrefixLength() {
        return prefixLength;
    }
    public static final char separatorChar = fs.getSeparator();
    public static final String separator = "" + separatorChar;
    public static final char pathSeparatorChar = fs.getPathSeparator();
    public static final String pathSeparator = "" + pathSeparatorChar;
    
    private File(String pathname, int prefixLength) {
        
        this.path = pathname;
        this.prefixLength = prefixLength;
    }
    
    private File(String child, File parent) {
        
        if (!$assertionsDisabled && !(parent.path != null)) throw new AssertionError();
        if (!$assertionsDisabled && !(!parent.path.equals(""))) throw new AssertionError();
        this.path = fs.resolve(parent.path, child);
        this.prefixLength = parent.prefixLength;
    }
    
    public File(String pathname) {
        
        if (pathname == null) {
            throw new NullPointerException();
        }
        this.path = fs.normalize(pathname);
        this.prefixLength = fs.prefixLength(this.path);
    }
    
    public File(String parent, String child) {
        
        if (child == null) {
            throw new NullPointerException();
        }
        if (parent != null) {
            if (parent.equals("")) {
                this.path = fs.resolve(fs.getDefaultParent(), fs.normalize(child));
            } else {
                this.path = fs.resolve(fs.normalize(parent), fs.normalize(child));
            }
        } else {
            this.path = fs.normalize(child);
        }
        this.prefixLength = fs.prefixLength(this.path);
    }
    
    public File(File parent, String child) {
        
        if (child == null) {
            throw new NullPointerException();
        }
        if (parent != null) {
            if (parent.path.equals("")) {
                this.path = fs.resolve(fs.getDefaultParent(), fs.normalize(child));
            } else {
                this.path = fs.resolve(parent.path, fs.normalize(child));
            }
        } else {
            this.path = fs.normalize(child);
        }
        this.prefixLength = fs.prefixLength(this.path);
    }
    
    public File(URI uri) {
        
        if (!uri.isAbsolute()) throw new IllegalArgumentException("URI is not absolute");
        if (uri.isOpaque()) throw new IllegalArgumentException("URI is not hierarchical");
        String scheme = uri.getScheme();
        if ((scheme == null) || !scheme.equalsIgnoreCase("file")) throw new IllegalArgumentException("URI scheme is not \"file\"");
        if (uri.getAuthority() != null) throw new IllegalArgumentException("URI has an authority component");
        if (uri.getFragment() != null) throw new IllegalArgumentException("URI has a fragment component");
        if (uri.getQuery() != null) throw new IllegalArgumentException("URI has a query component");
        String p = uri.getPath();
        if (p.equals("")) throw new IllegalArgumentException("URI path component is empty");
        p = fs.fromURIPath(p);
        if (File.separatorChar != '/') p = p.replace('/', File.separatorChar);
        this.path = fs.normalize(p);
        this.prefixLength = fs.prefixLength(this.path);
    }
    
    public String getName() {
        int index = path.lastIndexOf(separatorChar);
        if (index < prefixLength) return path.substring(prefixLength);
        return path.substring(index + 1);
    }
    
    public String getParent() {
        int index = path.lastIndexOf(separatorChar);
        if (index < prefixLength) {
            if ((prefixLength > 0) && (path.length() > prefixLength)) return path.substring(0, prefixLength);
            return null;
        }
        return path.substring(0, index);
    }
    
    public File getParentFile() {
        String p = this.getParent();
        if (p == null) return null;
        return new File(p, this.prefixLength);
    }
    
    public String getPath() {
        return path;
    }
    
    public boolean isAbsolute() {
        return fs.isAbsolute(this);
    }
    
    public String getAbsolutePath() {
        return fs.resolve(this);
    }
    
    public File getAbsoluteFile() {
        String absPath = getAbsolutePath();
        return new File(absPath, fs.prefixLength(absPath));
    }
    
    public String getCanonicalPath() throws IOException {
        return fs.canonicalize(fs.resolve(this));
    }
    
    public File getCanonicalFile() throws IOException {
        String canonPath = getCanonicalPath();
        return new File(canonPath, fs.prefixLength(canonPath));
    }
    
    private static String slashify(String path, boolean isDirectory) {
        String p = path;
        if (File.separatorChar != '/') p = p.replace(File.separatorChar, '/');
        if (!p.startsWith("/")) p = "/" + p;
        if (!p.endsWith("/") && isDirectory) p = p + "/";
        return p;
    }
    
    public URL toURL() throws MalformedURLException {
        return new URL("file", "", slashify(getAbsolutePath(), isDirectory()));
    }
    
    public URI toURI() {
        try {
            File f = getAbsoluteFile();
            String sp = slashify(f.getPath(), f.isDirectory());
            if (sp.startsWith("//")) sp = "//" + sp;
            return new URI("file", null, sp, null);
        } catch (URISyntaxException x) {
            throw new Error(x);
        }
    }
    
    public boolean canRead() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(path);
        }
        return fs.checkAccess(this, false);
    }
    
    public boolean canWrite() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkWrite(path);
        }
        return fs.checkAccess(this, true);
    }
    
    public boolean exists() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(path);
        }
        return ((fs.getBooleanAttributes(this) & FileSystem.BA_EXISTS) != 0);
    }
    
    public boolean isDirectory() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(path);
        }
        return ((fs.getBooleanAttributes(this) & FileSystem.BA_DIRECTORY) != 0);
    }
    
    public boolean isFile() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(path);
        }
        return ((fs.getBooleanAttributes(this) & FileSystem.BA_REGULAR) != 0);
    }
    
    public boolean isHidden() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(path);
        }
        return ((fs.getBooleanAttributes(this) & FileSystem.BA_HIDDEN) != 0);
    }
    
    public long lastModified() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(path);
        }
        return fs.getLastModifiedTime(this);
    }
    
    public long length() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(path);
        }
        return fs.getLength(this);
    }
    
    public boolean createNewFile() throws IOException {
        SecurityManager security = System.getSecurityManager();
        if (security != null) security.checkWrite(path);
        return fs.createFileExclusively(path);
    }
    
    public boolean delete() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkDelete(path);
        }
        return fs.delete(this);
    }
    
    public void deleteOnExit() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkDelete(path);
        }
        fs.deleteOnExit(this);
    }
    
    public String[] list() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(path);
        }
        return fs.list(this);
    }
    
    public String[] list(FilenameFilter filter) {
        String[] names = list();
        if ((names == null) || (filter == null)) {
            return names;
        }
        ArrayList v = new ArrayList();
        for (int i = 0; i < names.length; i++) {
            if (filter.accept(this, names[i])) {
                v.add(names[i]);
            }
        }
        return (String[])((String[])v.toArray(new String[0]));
    }
    
    public File[] listFiles() {
        String[] ss = list();
        if (ss == null) return null;
        int n = ss.length;
        File[] fs = new File[n];
        for (int i = 0; i < n; i++) {
            fs[i] = new File(ss[i], this);
        }
        return fs;
    }
    
    public File[] listFiles(FilenameFilter filter) {
        String[] ss = list();
        if (ss == null) return null;
        ArrayList v = new ArrayList();
        for (int i = 0; i < ss.length; i++) {
            if ((filter == null) || filter.accept(this, ss[i])) {
                v.add(new File(ss[i], this));
            }
        }
        return (File[])((File[])v.toArray(new File[0]));
    }
    
    public File[] listFiles(FileFilter filter) {
        String[] ss = list();
        if (ss == null) return null;
        ArrayList v = new ArrayList();
        for (int i = 0; i < ss.length; i++) {
            File f = new File(ss[i], this);
            if ((filter == null) || filter.accept(f)) {
                v.add(f);
            }
        }
        return (File[])((File[])v.toArray(new File[0]));
    }
    
    public boolean mkdir() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkWrite(path);
        }
        return fs.createDirectory(this);
    }
    
    public boolean mkdirs() {
        if (exists()) {
            return false;
        }
        if (mkdir()) {
            return true;
        }
        File canonFile = null;
        try {
            canonFile = getCanonicalFile();
        } catch (IOException e) {
            return false;
        }
        String parent = canonFile.getParent();
        return (parent != null) && (new File(parent, fs.prefixLength(parent)).mkdirs() && canonFile.mkdir());
    }
    
    public boolean renameTo(File dest) {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkWrite(path);
            security.checkWrite(dest.path);
        }
        return fs.rename(this, dest);
    }
    
    public boolean setLastModified(long time) {
        if (time < 0) throw new IllegalArgumentException("Negative time");
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkWrite(path);
        }
        return fs.setLastModifiedTime(this, time);
    }
    
    public boolean setReadOnly() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkWrite(path);
        }
        return fs.setReadOnly(this);
    }
    
    public static File[] listRoots() {
        return fs.listRoots();
    }
    {
    }
    
    private static File generateFile(String prefix, String suffix, File dir) throws IOException {
        long n = File$LazyInitialization.random.nextLong();
        if (n == Long.MIN_VALUE) {
            n = 0;
        } else {
            n = Math.abs(n);
        }
        return new File(dir, prefix + Long.toString(n) + suffix);
    }
    
    private static boolean checkAndCreate(String filename, SecurityManager sm) throws IOException {
        if (sm != null) {
            try {
                sm.checkWrite(filename);
            } catch (AccessControlException x) {
                throw new SecurityException("Unable to create temporary file");
            }
        }
        return fs.createFileExclusively(filename);
    }
    
    public static File createTempFile(String prefix, String suffix, File directory) throws IOException {
        if (prefix == null) throw new NullPointerException();
        if (prefix.length() < 3) throw new IllegalArgumentException("Prefix string too short");
        String s = (suffix == null) ? ".tmp" : suffix;
        if (directory == null) {
            String tmpDir = File$LazyInitialization.temporaryDirectory();
            directory = new File(tmpDir, fs.prefixLength(tmpDir));
        }
        SecurityManager sm = System.getSecurityManager();
        File f;
        do {
            f = generateFile(prefix, s, directory);
        }         while (!checkAndCreate(f.getPath(), sm));
        return f;
    }
    
    public static File createTempFile(String prefix, String suffix) throws IOException {
        return createTempFile(prefix, suffix, null);
    }
    
    public int compareTo(File pathname) {
        return fs.compare(this, pathname);
    }
    
    public boolean equals(Object obj) {
        if ((obj != null) && (obj instanceof File)) {
            return compareTo((File)(File)obj) == 0;
        }
        return false;
    }
    
    public int hashCode() {
        return fs.hashCode(this);
    }
    
    public String toString() {
        return getPath();
    }
    
    private synchronized void writeObject(java.io.ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        s.writeChar(this.separatorChar);
    }
    
    private synchronized void readObject(java.io.ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        char sep = s.readChar();
        if (sep != separatorChar) this.path = this.path.replace(sep, separatorChar);
        this.path = fs.normalize(this.path);
        this.prefixLength = fs.prefixLength(this.path);
    }
    private static final long serialVersionUID = 301077366599181567L;
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((File)x0);
    }
}
