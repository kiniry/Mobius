package java.util.jar;

import java.io.*;
import java.lang.ref.SoftReference;
import java.util.*;
import java.util.zip.*;
import java.security.AccessController;
import sun.security.action.GetPropertyAction;
import sun.security.util.ManifestEntryVerifier;
import sun.misc.SharedSecrets;

public class JarFile extends ZipFile {
    
    /*synthetic*/ static JarVerifier access$100(JarFile x0) {
        return x0.jv;
    }
    
    /*synthetic*/ static void access$000(JarFile x0) throws IOException {
        x0.maybeInstantiateVerifier();
    }
    private SoftReference manRef;
    private JarEntry manEntry;
    private JarVerifier jv;
    private boolean jvInitialized;
    private boolean verify;
    private boolean computedHasClassPathAttribute;
    private boolean hasClassPathAttribute;
    static {
        SharedSecrets.setJavaUtilJarAccess(new JavaUtilJarAccessImpl());
    }
    public static final String MANIFEST_NAME = "META-INF/MANIFEST.MF";
    
    public JarFile(String name) throws IOException {
        this(new File(name), true, ZipFile.OPEN_READ);
    }
    
    public JarFile(String name, boolean verify) throws IOException {
        this(new File(name), verify, ZipFile.OPEN_READ);
    }
    
    public JarFile(File file) throws IOException {
        this(file, true, ZipFile.OPEN_READ);
    }
    
    public JarFile(File file, boolean verify) throws IOException {
        this(file, verify, ZipFile.OPEN_READ);
    }
    
    public JarFile(File file, boolean verify, int mode) throws IOException {
        super(file, mode);
        this.verify = verify;
    }
    
    public Manifest getManifest() throws IOException {
        return getManifestFromReference();
    }
    
    private Manifest getManifestFromReference() throws IOException {
        Manifest man = manRef != null ? (Manifest)manRef.get() : null;
        if (man == null) {
            JarEntry manEntry = getManEntry();
            if (manEntry != null) {
                if (verify) {
                    byte[] b = getBytes(manEntry);
                    man = new Manifest(new ByteArrayInputStream(b));
                    if (!jvInitialized) {
                        jv = new JarVerifier(b);
                    }
                } else {
                    man = new Manifest(super.getInputStream(manEntry));
                }
                manRef = new SoftReference(man);
            }
        }
        return man;
    }
    
    private native String[] getMetaInfEntryNames();
    
    public JarEntry getJarEntry(String name) {
        return (JarEntry)(JarEntry)getEntry(name);
    }
    
    public ZipEntry getEntry(String name) {
        ZipEntry ze = super.getEntry(name);
        if (ze != null) {
            return new JarFile$JarFileEntry(this, ze);
        }
        return null;
    }
    
    public Enumeration entries() {
        final Enumeration enum_ = super.entries();
        return new JarFile$1(this, enum_);
    }
    {
    }
    
    private void maybeInstantiateVerifier() throws IOException {
        if (jv != null) {
            return;
        }
        if (verify) {
            String[] names = getMetaInfEntryNames();
            if (names != null) {
                for (int i = 0; i < names.length; i++) {
                    String name = names[i].toUpperCase(Locale.ENGLISH);
                    if (name.endsWith(".DSA") || name.endsWith(".RSA") || name.endsWith(".SF")) {
                        getManifest();
                        return;
                    }
                }
            }
            verify = false;
        }
    }
    
    private void initializeVerifier() {
        ManifestEntryVerifier mev = null;
        try {
            String[] names = getMetaInfEntryNames();
            if (names != null) {
                for (int i = 0; i < names.length; i++) {
                    JarEntry e = getJarEntry(names[i]);
                    if (!e.isDirectory()) {
                        if (mev == null) {
                            mev = new ManifestEntryVerifier(getManifestFromReference());
                        }
                        byte[] b = getBytes(e);
                        if (b != null && b.length > 0) {
                            jv.beginEntry(e, mev);
                            jv.update(b.length, b, 0, b.length, mev);
                            jv.update(-1, null, 0, 0, mev);
                        }
                    }
                }
            }
        } catch (IOException ex) {
            jv = null;
            verify = false;
        }
        if (jv != null) {
            jv.doneWithMeta();
            if (JarVerifier.debug != null) {
                JarVerifier.debug.println("done with meta!");
            }
            if (jv.nothingToVerify()) {
                if (JarVerifier.debug != null) {
                    JarVerifier.debug.println("nothing to verify!");
                }
                jv = null;
                verify = false;
            }
        }
    }
    
    private byte[] getBytes(ZipEntry ze) throws IOException {
        byte[] b = new byte[(int)ze.getSize()];
        DataInputStream is = new DataInputStream(super.getInputStream(ze));
        is.readFully(b, 0, b.length);
        is.close();
        return b;
    }
    
    public synchronized InputStream getInputStream(ZipEntry ze) throws IOException {
        maybeInstantiateVerifier();
        if (jv == null) {
            return super.getInputStream(ze);
        }
        if (!jvInitialized) {
            initializeVerifier();
            jvInitialized = true;
            if (jv == null) return super.getInputStream(ze);
        }
        return new JarVerifier$VerifierStream(getManifestFromReference(), ze instanceof JarFile$JarFileEntry ? (JarEntry)(JarEntry)ze : getJarEntry(ze.getName()), super.getInputStream(ze), jv);
    }
    private static int[] lastOcc;
    private static int[] optoSft;
    private static char[] src = {'c', 'l', 'a', 's', 's', '-', 'p', 'a', 't', 'h'};
    static {
        lastOcc = new int[128];
        optoSft = new int[10];
        lastOcc[(int)'c'] = 1;
        lastOcc[(int)'l'] = 2;
        lastOcc[(int)'s'] = 5;
        lastOcc[(int)'-'] = 6;
        lastOcc[(int)'p'] = 7;
        lastOcc[(int)'a'] = 8;
        lastOcc[(int)'t'] = 9;
        lastOcc[(int)'h'] = 10;
        for (int i = 0; i < 9; i++) optoSft[i] = 10;
        optoSft[9] = 1;
    }
    
    private JarEntry getManEntry() {
        if (manEntry == null) {
            manEntry = getJarEntry(MANIFEST_NAME);
            if (manEntry == null) {
                String[] names = getMetaInfEntryNames();
                if (names != null) {
                    for (int i = 0; i < names.length; i++) {
                        if (MANIFEST_NAME.equals(names[i].toUpperCase(Locale.ENGLISH))) {
                            manEntry = getJarEntry(names[i]);
                            break;
                        }
                    }
                }
            }
        }
        return manEntry;
    }
    
    boolean hasClassPathAttribute() throws IOException {
        if (computedHasClassPathAttribute) {
            return hasClassPathAttribute;
        }
        hasClassPathAttribute = false;
        if (!isKnownToNotHaveClassPathAttribute()) {
            JarEntry manEntry = getManEntry();
            if (manEntry != null) {
                byte[] b = new byte[(int)manEntry.getSize()];
                DataInputStream dis = new DataInputStream(super.getInputStream(manEntry));
                dis.readFully(b, 0, b.length);
                dis.close();
                int last = b.length - src.length;
                int i = 0;
                next: while (i <= last) {
                    for (int j = 9; j >= 0; j--) {
                        char c = (char)b[i + j];
                        c = (((c - 'A') | ('Z' - c)) >= 0) ? (char)(c + 32) : c;
                        if (c != src[j]) {
                            i += Math.max(j + 1 - lastOcc[c & 127], optoSft[j]);
                            continue next;
                        }
                    }
                    hasClassPathAttribute = true;
                    break;
                }
            }
        }
        computedHasClassPathAttribute = true;
        return hasClassPathAttribute;
    }
    private static String javaHome;
    
    private boolean isKnownToNotHaveClassPathAttribute() {
        if (javaHome == null) {
            javaHome = (String)(String)AccessController.doPrivileged(new GetPropertyAction("java.home"));
        }
        String name = getName();
        String localJavaHome = javaHome;
        if (name.startsWith(localJavaHome)) {
            if (name.endsWith("rt.jar") || name.endsWith("sunrsasign.jar") || name.endsWith("jsse.jar") || name.endsWith("jce.jar") || name.endsWith("charsets.jar") || name.endsWith("dnsns.jar") || name.endsWith("ldapsec.jar") || name.endsWith("localedata.jar") || name.endsWith("sunjce_provider.jar")) {
                return true;
            }
        }
        return false;
    }
}
