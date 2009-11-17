package java.util.jar;

import java.io.*;
import java.util.*;
import java.util.zip.*;
import java.security.CodeSigner;
import java.security.cert.Certificate;

class JarFile$JarFileEntry extends JarEntry {
    /*synthetic*/ final JarFile this$0;
    
    JarFile$JarFileEntry(/*synthetic*/ final JarFile this$0, ZipEntry ze) {
        super( this.this$0 = ze);
    }
    
    public Attributes getAttributes() throws IOException {
        Manifest man = this$0.getManifest();
        if (man != null) {
            return man.getAttributes(getName());
        } else {
            return null;
        }
    }
    
    public java.security.cert.Certificate[] getCertificates() {
        try {
            JarFile.access$000(this$0);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        if (certs == null && JarFile.access$100(this$0) != null) {
            Certificate[] cs = JarFile.access$100(this$0).getCerts(getName());
            if (cs != null) {
                certs = (Certificate[])(Certificate[])cs.clone();
            }
        }
        return certs;
    }
    
    public CodeSigner[] getCodeSigners() {
        try {
            JarFile.access$000(this$0);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        if (signers == null && JarFile.access$100(this$0) != null) {
            CodeSigner[] csg = JarFile.access$100(this$0).getCodeSigners(getName());
            if (csg != null) {
                signers = (CodeSigner[])(CodeSigner[])csg.clone();
            }
        }
        return signers;
    }
}
