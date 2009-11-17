package java.util.jar;

import java.io.IOException;
import java.util.zip.ZipEntry;
import java.security.CodeSigner;
import java.security.cert.Certificate;

public class JarEntry extends ZipEntry {
    Attributes attr;
    Certificate[] certs;
    CodeSigner[] signers;
    
    public JarEntry(String name) {
        super(name);
    }
    
    public JarEntry(ZipEntry ze) {
        super(ze);
    }
    
    public JarEntry(JarEntry je) {
        this((ZipEntry)je);
        this.attr = je.attr;
        this.certs = je.certs;
        this.signers = je.signers;
    }
    
    public Attributes getAttributes() throws IOException {
        return attr;
    }
    
    public Certificate[] getCertificates() {
        return certs;
    }
    
    public CodeSigner[] getCodeSigners() {
        return signers;
    }
}
