package java.util.jar;

import java.io.*;
import java.util.*;
import java.util.zip.*;
import java.security.*;
import java.security.cert.CertificateException;
import sun.security.util.ManifestDigester;
import sun.security.util.ManifestEntryVerifier;
import sun.security.util.SignatureFileVerifier;
import sun.security.util.Debug;

class JarVerifier {
    static final Debug debug = Debug.getInstance("jar");
    private Hashtable verifiedSigners;
    private Hashtable sigFileSigners;
    private Hashtable sigFileData;
    private ArrayList pendingBlocks;
    private ArrayList signerCache;
    private boolean parsingBlockOrSF = false;
    private boolean parsingMeta = true;
    private boolean anyToVerify = true;
    private ByteArrayOutputStream baos;
    private ManifestDigester manDig;
    byte[] manifestRawBytes = null;
    
    public JarVerifier(byte[] rawBytes) {
        
        manifestRawBytes = rawBytes;
        sigFileSigners = new Hashtable();
        verifiedSigners = new Hashtable();
        sigFileData = new Hashtable(11);
        pendingBlocks = new ArrayList();
        baos = new ByteArrayOutputStream();
    }
    
    public void beginEntry(JarEntry je, ManifestEntryVerifier mev) throws IOException {
        if (je == null) return;
        if (debug != null) {
            debug.println("beginEntry " + je.getName());
        }
        String name = je.getName();
        if (parsingMeta) {
            String uname = name.toUpperCase(Locale.ENGLISH);
            if (uname.startsWith("META-INF/") || uname.startsWith("/META-INF/")) {
                if (je.isDirectory()) {
                    mev.setEntry(null, je);
                    return;
                }
                if (SignatureFileVerifier.isBlockOrSF(uname)) {
                    parsingBlockOrSF = true;
                    baos.reset();
                    mev.setEntry(null, je);
                }
                return;
            }
        }
        if (parsingMeta) {
            doneWithMeta();
        }
        if (je.isDirectory()) {
            mev.setEntry(null, je);
            return;
        }
        if (name.startsWith("./")) name = name.substring(2);
        if (name.startsWith("/")) name = name.substring(1);
        if (sigFileSigners.get(name) != null) {
            mev.setEntry(name, je);
            return;
        }
        mev.setEntry(null, je);
        return;
    }
    
    public void update(int b, ManifestEntryVerifier mev) throws IOException {
        if (b != -1) {
            if (parsingBlockOrSF) {
                baos.write(b);
            } else {
                mev.update((byte)b);
            }
        } else {
            processEntry(mev);
        }
    }
    
    public void update(int n, byte[] b, int off, int len, ManifestEntryVerifier mev) throws IOException {
        if (n != -1) {
            if (parsingBlockOrSF) {
                baos.write(b, off, n);
            } else {
                mev.update(b, off, n);
            }
        } else {
            processEntry(mev);
        }
    }
    
    private void processEntry(ManifestEntryVerifier mev) throws IOException {
        if (!parsingBlockOrSF) {
            JarEntry je = mev.getEntry();
            if ((je != null) && (je.signers == null)) {
                je.signers = mev.verify(verifiedSigners, sigFileSigners);
            }
        } else {
            try {
                parsingBlockOrSF = false;
                if (debug != null) {
                    debug.println("processEntry: processing block");
                }
                String uname = mev.getEntry().getName().toUpperCase(Locale.ENGLISH);
                if (uname.endsWith(".SF")) {
                    String key = uname.substring(0, uname.length() - 3);
                    byte[] bytes = baos.toByteArray();
                    sigFileData.put(key, bytes);
                    Iterator it = pendingBlocks.iterator();
                    while (it.hasNext()) {
                        SignatureFileVerifier sfv = (SignatureFileVerifier)(SignatureFileVerifier)it.next();
                        if (sfv.needSignatureFile(key)) {
                            if (debug != null) {
                                debug.println("processEntry: processing pending block");
                            }
                            sfv.setSignatureFile(bytes);
                            sfv.process(sigFileSigners);
                        }
                    }
                    return;
                }
                String key = uname.substring(0, uname.lastIndexOf("."));
                if (signerCache == null) signerCache = new ArrayList();
                if (manDig == null) {
                    synchronized (manifestRawBytes) {
                        if (manDig == null) {
                            manDig = new ManifestDigester(manifestRawBytes);
                            manifestRawBytes = null;
                        }
                    }
                }
                SignatureFileVerifier sfv = new SignatureFileVerifier(signerCache, manDig, uname, baos.toByteArray());
                if (sfv.needSignatureFileBytes()) {
                    byte[] bytes = (byte[])(byte[])sigFileData.get(key);
                    if (bytes == null) {
                        if (debug != null) {
                            debug.println("adding pending block");
                        }
                        pendingBlocks.add(sfv);
                        return;
                    } else {
                        sfv.setSignatureFile(bytes);
                    }
                }
                sfv.process(sigFileSigners);
            } catch (sun.security.pkcs.ParsingException pe) {
                if (debug != null) debug.println("processEntry caught: " + pe);
            } catch (IOException ioe) {
                if (debug != null) debug.println("processEntry caught: " + ioe);
            } catch (SignatureException se) {
                if (debug != null) debug.println("processEntry caught: " + se);
            } catch (NoSuchAlgorithmException nsae) {
                if (debug != null) debug.println("processEntry caught: " + nsae);
            } catch (CertificateException ce) {
                if (debug != null) debug.println("processEntry caught: " + ce);
            }
        }
    }
    
    public java.security.cert.Certificate[] getCerts(String name) {
        CodeSigner[] signers = getCodeSigners(name);
        if (signers != null) {
            ArrayList certChains = new ArrayList();
            for (int i = 0; i < signers.length; i++) {
                certChains.addAll(signers[i].getSignerCertPath().getCertificates());
            }
            return (java.security.cert.Certificate[])(java.security.cert.Certificate[])certChains.toArray(new java.security.cert.Certificate[certChains.size()]);
        }
        return null;
    }
    
    public CodeSigner[] getCodeSigners(String name) {
        return (CodeSigner[])(CodeSigner[])verifiedSigners.get(name);
    }
    
    boolean nothingToVerify() {
        return (anyToVerify == false);
    }
    
    void doneWithMeta() {
        parsingMeta = false;
        anyToVerify = !sigFileSigners.isEmpty();
        baos = null;
        sigFileData = null;
        pendingBlocks = null;
        signerCache = null;
        manDig = null;
    }
    {
    }
}
