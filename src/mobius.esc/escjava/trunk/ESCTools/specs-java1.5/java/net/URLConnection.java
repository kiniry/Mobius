package java.net;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Hashtable;
import java.util.Date;
import java.util.StringTokenizer;
import java.util.Collections;
import java.util.Map;
import java.security.Permission;
import java.security.AccessController;
import sun.security.util.SecurityConstants;

public abstract class URLConnection {
    
    /*synthetic*/ static FileNameMap access$000() {
        return fileNameMap;
    }
    protected URL url;
    protected boolean doInput = true;
    protected boolean doOutput = false;
    private static boolean defaultAllowUserInteraction = false;
    protected boolean allowUserInteraction = defaultAllowUserInteraction;
    private static boolean defaultUseCaches = true;
    protected boolean useCaches = defaultUseCaches;
    protected long ifModifiedSince = 0;
    protected boolean connected = false;
    private int connectTimeout;
    private int readTimeout;
    private static FileNameMap fileNameMap;
    private static boolean fileNameMapLoaded = false;
    
    public static synchronized FileNameMap getFileNameMap() {
        if ((fileNameMap == null) && !fileNameMapLoaded) {
            fileNameMap = sun.net.www.MimeTable.loadTable();
            fileNameMapLoaded = true;
        }
        return new URLConnection$1();
    }
    
    public static void setFileNameMap(FileNameMap map) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkSetFactory();
        fileNameMap = map;
    }
    
    public abstract void connect() throws IOException;
    
    public void setConnectTimeout(int timeout) {
        if (timeout < 0) {
            throw new IllegalArgumentException("timeout can not be negative");
        }
        connectTimeout = timeout;
    }
    
    public int getConnectTimeout() {
        return connectTimeout;
    }
    
    public void setReadTimeout(int timeout) {
        if (timeout < 0) {
            throw new IllegalArgumentException("timeout can not be negative");
        }
        readTimeout = timeout;
    }
    
    public int getReadTimeout() {
        return readTimeout;
    }
    
    protected URLConnection(URL url) {
        
        this.url = url;
    }
    
    public URL getURL() {
        return url;
    }
    
    public int getContentLength() {
        return getHeaderFieldInt("content-length", -1);
    }
    
    public String getContentType() {
        return getHeaderField("content-type");
    }
    
    public String getContentEncoding() {
        return getHeaderField("content-encoding");
    }
    
    public long getExpiration() {
        return getHeaderFieldDate("expires", 0);
    }
    
    public long getDate() {
        return getHeaderFieldDate("date", 0);
    }
    
    public long getLastModified() {
        return getHeaderFieldDate("last-modified", 0);
    }
    
    public String getHeaderField(String name) {
        return null;
    }
    
    public Map getHeaderFields() {
        return Collections.EMPTY_MAP;
    }
    
    public int getHeaderFieldInt(String name, int Default) {
        String value = getHeaderField(name);
        try {
            return Integer.parseInt(value);
        } catch (Exception e) {
        }
        return Default;
    }
    
    public long getHeaderFieldDate(String name, long Default) {
        String value = getHeaderField(name);
        try {
            return Date.parse(value);
        } catch (Exception e) {
        }
        return Default;
    }
    
    public String getHeaderFieldKey(int n) {
        return null;
    }
    
    public String getHeaderField(int n) {
        return null;
    }
    
    public Object getContent() throws IOException {
        getInputStream();
        return getContentHandler().getContent(this);
    }
    
    public Object getContent(Class[] classes) throws IOException {
        getInputStream();
        return getContentHandler().getContent(this, classes);
    }
    
    public Permission getPermission() throws IOException {
        return SecurityConstants.ALL_PERMISSION;
    }
    
    public InputStream getInputStream() throws IOException {
        throw new UnknownServiceException("protocol doesn\'t support input");
    }
    
    public OutputStream getOutputStream() throws IOException {
        throw new UnknownServiceException("protocol doesn\'t support output");
    }
    
    public String toString() {
        return this.getClass().getName() + ":" + url;
    }
    
    public void setDoInput(boolean doinput) {
        if (connected) throw new IllegalStateException("Already connected");
        doInput = doinput;
    }
    
    public boolean getDoInput() {
        return doInput;
    }
    
    public void setDoOutput(boolean dooutput) {
        if (connected) throw new IllegalStateException("Already connected");
        doOutput = dooutput;
    }
    
    public boolean getDoOutput() {
        return doOutput;
    }
    
    public void setAllowUserInteraction(boolean allowuserinteraction) {
        if (connected) throw new IllegalStateException("Already connected");
        allowUserInteraction = allowuserinteraction;
    }
    
    public boolean getAllowUserInteraction() {
        return allowUserInteraction;
    }
    
    public static void setDefaultAllowUserInteraction(boolean defaultallowuserinteraction) {
        defaultAllowUserInteraction = defaultallowuserinteraction;
    }
    
    public static boolean getDefaultAllowUserInteraction() {
        return defaultAllowUserInteraction;
    }
    
    public void setUseCaches(boolean usecaches) {
        if (connected) throw new IllegalStateException("Already connected");
        useCaches = usecaches;
    }
    
    public boolean getUseCaches() {
        return useCaches;
    }
    
    public void setIfModifiedSince(long ifmodifiedsince) {
        if (connected) throw new IllegalStateException("Already connected");
        ifModifiedSince = ifmodifiedsince;
    }
    
    public long getIfModifiedSince() {
        return ifModifiedSince;
    }
    
    public boolean getDefaultUseCaches() {
        return defaultUseCaches;
    }
    
    public void setDefaultUseCaches(boolean defaultusecaches) {
        defaultUseCaches = defaultusecaches;
    }
    
    public void setRequestProperty(String key, String value) {
        if (connected) throw new IllegalStateException("Already connected");
        if (key == null) throw new NullPointerException("key is null");
    }
    
    public void addRequestProperty(String key, String value) {
        if (connected) throw new IllegalStateException("Already connected");
        if (key == null) throw new NullPointerException("key is null");
    }
    
    public String getRequestProperty(String key) {
        if (connected) throw new IllegalStateException("Already connected");
        return null;
    }
    
    public Map getRequestProperties() {
        if (connected) throw new IllegalStateException("Already connected");
        return Collections.EMPTY_MAP;
    }
    
    
    public static void setDefaultRequestProperty(String key, String value) {
    }
    
    
    public static String getDefaultRequestProperty(String key) {
        return null;
    }
    static ContentHandlerFactory factory;
    
    public static synchronized void setContentHandlerFactory(ContentHandlerFactory fac) {
        if (factory != null) {
            throw new Error("factory already defined");
        }
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkSetFactory();
        }
        factory = fac;
    }
    private static Hashtable handlers = new Hashtable();
    private static final ContentHandler UnknownContentHandlerP = new UnknownContentHandler();
    
    synchronized ContentHandler getContentHandler() throws UnknownServiceException {
        String contentType = stripOffParameters(getContentType());
        ContentHandler handler = null;
        if (contentType == null) throw new UnknownServiceException("no content-type");
        try {
            handler = (ContentHandler)(ContentHandler)handlers.get(contentType);
            if (handler != null) return handler;
        } catch (Exception e) {
        }
        if (factory != null) handler = factory.createContentHandler(contentType);
        if (handler == null) {
            try {
                handler = lookupContentHandlerClassFor(contentType);
            } catch (Exception e) {
                e.printStackTrace();
                handler = UnknownContentHandlerP;
            }
            handlers.put(contentType, handler);
        }
        return handler;
    }
    
    private String stripOffParameters(String contentType) {
        if (contentType == null) return null;
        int index = contentType.indexOf(';');
        if (index > 0) return contentType.substring(0, index); else return contentType;
    }
    private static final String contentClassPrefix = "sun.net.www.content";
    private static final String contentPathProp = "java.content.handler.pkgs";
    
    private ContentHandler lookupContentHandlerClassFor(String contentType) throws InstantiationException, IllegalAccessException, ClassNotFoundException {
        String contentHandlerClassName = typeToPackageName(contentType);
        String contentHandlerPkgPrefixes = getContentHandlerPkgPrefixes();
        StringTokenizer packagePrefixIter = new StringTokenizer(contentHandlerPkgPrefixes, "|");
        while (packagePrefixIter.hasMoreTokens()) {
            String packagePrefix = packagePrefixIter.nextToken().trim();
            try {
                String clsName = packagePrefix + "." + contentHandlerClassName;
                Class cls = null;
                try {
                    cls = Class.forName(clsName);
                } catch (ClassNotFoundException e) {
                    ClassLoader cl = ClassLoader.getSystemClassLoader();
                    if (cl != null) {
                        cls = cl.loadClass(clsName);
                    }
                }
                if (cls != null) {
                    ContentHandler handler = (ContentHandler)(ContentHandler)cls.newInstance();
                    return handler;
                }
            } catch (Exception e) {
            }
        }
        return UnknownContentHandlerP;
    }
    
    private String typeToPackageName(String contentType) {
        contentType = contentType.toLowerCase();
        int len = contentType.length();
        char[] nm = new char[len];
        contentType.getChars(0, len, nm, 0);
        for (int i = 0; i < len; i++) {
            char c = nm[i];
            if (c == '/') {
                nm[i] = '.';
            } else if (!('A' <= c && c <= 'Z' || 'a' <= c && c <= 'z' || '0' <= c && c <= '9')) {
                nm[i] = '_';
            }
        }
        return new String(nm);
    }
    
    private String getContentHandlerPkgPrefixes() {
        String packagePrefixList = (String)(String)AccessController.doPrivileged(new sun.security.action.GetPropertyAction(contentPathProp, ""));
        if (packagePrefixList != "") {
            packagePrefixList += "|";
        }
        return packagePrefixList + contentClassPrefix;
    }
    
    public static String guessContentTypeFromName(String fname) {
        return getFileNameMap().getContentTypeFor(fname);
    }
    
    public static String guessContentTypeFromStream(InputStream is) throws IOException {
        if (!is.markSupported()) return null;
        is.mark(12);
        int c1 = is.read();
        int c2 = is.read();
        int c3 = is.read();
        int c4 = is.read();
        int c5 = is.read();
        int c6 = is.read();
        int c7 = is.read();
        int c8 = is.read();
        int c9 = is.read();
        int c10 = is.read();
        int c11 = is.read();
        is.reset();
        if (c1 == 202 && c2 == 254 && c3 == 186 && c4 == 190) {
            return "application/java-vm";
        }
        if (c1 == 172 && c2 == 237) {
            return "application/x-java-serialized-object";
        }
        if (c1 == '<') {
            if (c2 == '!' || ((c2 == 'h' && (c3 == 't' && c4 == 'm' && c5 == 'l' || c3 == 'e' && c4 == 'a' && c5 == 'd') || (c2 == 'b' && c3 == 'o' && c4 == 'd' && c5 == 'y'))) || ((c2 == 'H' && (c3 == 'T' && c4 == 'M' && c5 == 'L' || c3 == 'E' && c4 == 'A' && c5 == 'D') || (c2 == 'B' && c3 == 'O' && c4 == 'D' && c5 == 'Y')))) {
                return "text/html";
            }
            if (c2 == '?' && c3 == 'x' && c4 == 'm' && c5 == 'l' && c6 == ' ') {
                return "application/xml";
            }
        }
        if (c1 == 254 && c2 == 255) {
            if (c3 == 0 && c4 == '<' && c5 == 0 && c6 == '?' && c7 == 0 && c8 == 'x') {
                return "application/xml";
            }
        }
        if (c1 == 255 && c2 == 254) {
            if (c3 == '<' && c4 == 0 && c5 == '?' && c6 == 0 && c7 == 'x' && c8 == 0) {
                return "application/xml";
            }
        }
        if (c1 == 'G' && c2 == 'I' && c3 == 'F' && c4 == '8') {
            return "image/gif";
        }
        if (c1 == '#' && c2 == 'd' && c3 == 'e' && c4 == 'f') {
            return "image/x-bitmap";
        }
        if (c1 == '!' && c2 == ' ' && c3 == 'X' && c4 == 'P' && c5 == 'M' && c6 == '2') {
            return "image/x-pixmap";
        }
        if (c1 == 137 && c2 == 80 && c3 == 78 && c4 == 71 && c5 == 13 && c6 == 10 && c7 == 26 && c8 == 10) {
            return "image/png";
        }
        if (c1 == 255 && c2 == 216 && c3 == 255) {
            if (c4 == 224) {
                return "image/jpeg";
            }
            if ((c4 == 225) && (c7 == 'E' && c8 == 'x' && c9 == 'i' && c10 == 'f' && c11 == 0)) {
                return "image/jpeg";
            }
            if (c4 == 238) {
                return "image/jpg";
            }
        }
        if (c1 == 208 && c2 == 207 && c3 == 17 && c4 == 224 && c5 == 161 && c6 == 177 && c7 == 26 && c8 == 225) {
            if (checkfpx(is)) {
                return "image/vnd.fpx";
            }
        }
        if (c1 == 46 && c2 == 115 && c3 == 110 && c4 == 100) {
            return "audio/basic";
        }
        if (c1 == 100 && c2 == 110 && c3 == 115 && c4 == 46) {
            return "audio/basic";
        }
        if (c1 == 'R' && c2 == 'I' && c3 == 'F' && c4 == 'F') {
            return "audio/x-wav";
        }
        return null;
    }
    
    private static boolean checkfpx(InputStream is) throws IOException {
        is.mark(256);
        long toSkip = (long)28;
        long posn;
        if ((posn = skipForward(is, toSkip)) < toSkip) {
            is.reset();
            return false;
        }
        int[] c = new int[16];
        if (readBytes(c, 2, is) < 0) {
            is.reset();
            return false;
        }
        int byteOrder = c[0];
        posn += 2;
        int uSectorShift;
        if (readBytes(c, 2, is) < 0) {
            is.reset();
            return false;
        }
        if (byteOrder == 254) {
            uSectorShift = c[0];
            uSectorShift += c[1] << 8;
        } else {
            uSectorShift = c[0] << 8;
            uSectorShift += c[1];
        }
        posn += 2;
        toSkip = (long)48 - posn;
        long skipped = 0;
        if ((skipped = skipForward(is, toSkip)) < toSkip) {
            is.reset();
            return false;
        }
        posn += skipped;
        if (readBytes(c, 4, is) < 0) {
            is.reset();
            return false;
        }
        int sectDirStart;
        if (byteOrder == 254) {
            sectDirStart = c[0];
            sectDirStart += c[1] << 8;
            sectDirStart += c[2] << 16;
            sectDirStart += c[3] << 24;
        } else {
            sectDirStart = c[0] << 24;
            sectDirStart += c[1] << 16;
            sectDirStart += c[2] << 8;
            sectDirStart += c[3];
        }
        posn += 4;
        is.reset();
        toSkip = (long)512 + (long)((int)1 << uSectorShift) * sectDirStart + (long)80;
        if (toSkip < 0) {
            return false;
        }
        is.mark((int)toSkip + 48);
        if ((skipForward(is, toSkip)) < toSkip) {
            is.reset();
            return false;
        }
        if (readBytes(c, 16, is) < 0) {
            is.reset();
            return false;
        }
        if (byteOrder == 254 && c[0] == 0 && c[2] == 97 && c[3] == 86 && c[4] == 84 && c[5] == 193 && c[6] == 206 && c[7] == 17 && c[8] == 133 && c[9] == 83 && c[10] == 0 && c[11] == 170 && c[12] == 0 && c[13] == 161 && c[14] == 249 && c[15] == 91) {
            is.reset();
            return true;
        } else if (c[3] == 0 && c[1] == 97 && c[0] == 86 && c[5] == 84 && c[4] == 193 && c[7] == 206 && c[6] == 17 && c[8] == 133 && c[9] == 83 && c[10] == 0 && c[11] == 170 && c[12] == 0 && c[13] == 161 && c[14] == 249 && c[15] == 91) {
            is.reset();
            return true;
        }
        is.reset();
        return false;
    }
    
    private static int readBytes(int[] c, int len, InputStream is) throws IOException {
        byte[] buf = new byte[len];
        if (is.read(buf, 0, len) < len) {
            return -1;
        }
        for (int i = 0; i < len; i++) {
            c[i] = buf[i] & 255;
        }
        return 0;
    }
    
    private static long skipForward(InputStream is, long toSkip) throws IOException {
        long eachSkip = 0;
        long skipped = 0;
        while (skipped != toSkip) {
            eachSkip = is.skip(toSkip - skipped);
            if (eachSkip <= 0) {
                if (is.read() == -1) {
                    return skipped;
                } else {
                    skipped++;
                }
            }
            skipped += eachSkip;
        }
        return skipped;
    }
}
