package java.net;

import java.io.IOException;
import java.util.jar.JarFile;
import java.util.jar.JarEntry;
import java.util.jar.Attributes;
import java.util.jar.Manifest;
import sun.net.www.ParseUtil;

public abstract class JarURLConnection extends URLConnection {
    private URL jarFileURL;
    private String entryName;
    protected URLConnection jarFileURLConnection;
    
    protected JarURLConnection(URL url) throws MalformedURLException {
        super(url);
        parseSpecs(url);
    }
    
    private void parseSpecs(URL url) throws MalformedURLException {
        String spec = url.getFile();
        int separator = spec.indexOf('!');
        if (separator == -1) {
            throw new MalformedURLException("no ! found in url spec:" + spec);
        }
        jarFileURL = new URL(spec.substring(0, separator++));
        entryName = null;
        if (++separator != spec.length()) {
            entryName = spec.substring(separator, spec.length());
            entryName = ParseUtil.decode(entryName);
        }
    }
    
    public URL getJarFileURL() {
        return jarFileURL;
    }
    
    public String getEntryName() {
        return entryName;
    }
    
    public abstract JarFile getJarFile() throws IOException;
    
    public Manifest getManifest() throws IOException {
        return getJarFile().getManifest();
    }
    
    public JarEntry getJarEntry() throws IOException {
        return getJarFile().getJarEntry(entryName);
    }
    
    public Attributes getAttributes() throws IOException {
        JarEntry e = getJarEntry();
        return e != null ? e.getAttributes() : null;
    }
    
    public Attributes getMainAttributes() throws IOException {
        Manifest man = getManifest();
        return man != null ? man.getMainAttributes() : null;
    }
    
    public java.security.cert.Certificate[] getCertificates() throws IOException {
        JarEntry e = getJarEntry();
        return e != null ? e.getCertificates() : null;
    }
}
