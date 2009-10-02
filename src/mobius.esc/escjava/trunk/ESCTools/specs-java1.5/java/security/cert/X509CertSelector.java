package java.security.cert;

import java.io.IOException;
import java.math.BigInteger;
import java.security.PublicKey;
import java.util.*;
import javax.security.auth.x500.X500Principal;
import sun.misc.HexDumpEncoder;
import sun.security.util.Debug;
import sun.security.util.DerInputStream;
import sun.security.util.DerValue;
import sun.security.util.ObjectIdentifier;
import sun.security.x509.*;

public class X509CertSelector implements CertSelector {
    private static final Debug debug = Debug.getInstance("certpath");
    private static final ObjectIdentifier ANY_EXTENDED_KEY_USAGE = ObjectIdentifier.newInternal(new int[]{2, 5, 29, 37, 0});
    static {
        CertPathHelperImpl.initialize();
    }
    private BigInteger serialNumber;
    private X500Principal issuer;
    private X500Principal subject;
    private byte[] subjectKeyID;
    private byte[] authorityKeyID;
    private Date certificateValid;
    private Date privateKeyValid;
    private ObjectIdentifier subjectPublicKeyAlgID;
    private PublicKey subjectPublicKey;
    private byte[] subjectPublicKeyBytes;
    private boolean[] keyUsage;
    private Set keyPurposeSet;
    private Set keyPurposeOIDSet;
    private Set subjectAlternativeNames;
    private Set subjectAlternativeGeneralNames;
    private CertificatePolicySet policy;
    private Set policySet;
    private Set pathToNames;
    private Set pathToGeneralNames;
    private NameConstraintsExtension nc;
    private byte[] ncBytes;
    private int basicConstraints = -1;
    private X509Certificate x509Cert;
    private boolean matchAllSubjectAltNames = true;
    private static final Boolean FALSE = Boolean.FALSE;
    private static final int PRIVATE_KEY_USAGE_ID = 0;
    private static final int SUBJECT_ALT_NAME_ID = 1;
    private static final int NAME_CONSTRAINTS_ID = 2;
    private static final int CERT_POLICIES_ID = 3;
    private static final int EXTENDED_KEY_USAGE_ID = 4;
    private static final int NUM_OF_EXTENSIONS = 5;
    private static final String[] EXTENSION_OIDS = new String[NUM_OF_EXTENSIONS];
    static {
        EXTENSION_OIDS[PRIVATE_KEY_USAGE_ID] = "2.5.29.16";
        EXTENSION_OIDS[SUBJECT_ALT_NAME_ID] = "2.5.29.17";
        EXTENSION_OIDS[NAME_CONSTRAINTS_ID] = "2.5.29.30";
        EXTENSION_OIDS[CERT_POLICIES_ID] = "2.5.29.32";
        EXTENSION_OIDS[EXTENDED_KEY_USAGE_ID] = "2.5.29.37";
    }
    {
    }
    static final int NAME_ANY = 0;
    static final int NAME_RFC822 = 1;
    static final int NAME_DNS = 2;
    static final int NAME_X400 = 3;
    static final int NAME_DIRECTORY = 4;
    static final int NAME_EDI = 5;
    static final int NAME_URI = 6;
    static final int NAME_IP = 7;
    static final int NAME_OID = 8;
    
    public X509CertSelector() {
        
    }
    
    public void setCertificate(X509Certificate cert) {
        x509Cert = cert;
    }
    
    public void setSerialNumber(BigInteger serial) {
        serialNumber = serial;
    }
    
    public void setIssuer(X500Principal issuer) {
        this.issuer = issuer;
    }
    
    public void setIssuer(String issuerDN) throws IOException {
        if (issuerDN == null) {
            issuer = null;
        } else {
            issuer = new X500Name(issuerDN).asX500Principal();
        }
    }
    
    public void setIssuer(byte[] issuerDN) throws IOException {
        try {
            issuer = (issuerDN == null ? null : new X500Principal(issuerDN));
        } catch (IllegalArgumentException e) {
            throw (IOException)(IOException)new IOException("Invalid name").initCause(e);
        }
    }
    
    public void setSubject(X500Principal subject) {
        this.subject = subject;
    }
    
    public void setSubject(String subjectDN) throws IOException {
        if (subjectDN == null) {
            subject = null;
        } else {
            subject = new X500Name(subjectDN).asX500Principal();
        }
    }
    
    public void setSubject(byte[] subjectDN) throws IOException {
        try {
            subject = (subjectDN == null ? null : new X500Principal(subjectDN));
        } catch (IllegalArgumentException e) {
            throw (IOException)(IOException)new IOException("Invalid name").initCause(e);
        }
    }
    
    public void setSubjectKeyIdentifier(byte[] subjectKeyID) {
        if (subjectKeyID == null) {
            this.subjectKeyID = null;
        } else {
            this.subjectKeyID = (byte[])(byte[])subjectKeyID.clone();
        }
    }
    
    public void setAuthorityKeyIdentifier(byte[] authorityKeyID) {
        if (authorityKeyID == null) {
            this.authorityKeyID = null;
        } else {
            this.authorityKeyID = (byte[])(byte[])authorityKeyID.clone();
        }
    }
    
    public void setCertificateValid(Date certValid) {
        if (certValid == null) {
            certificateValid = null;
        } else {
            certificateValid = (Date)(Date)certValid.clone();
        }
    }
    
    public void setPrivateKeyValid(Date privateKeyValid) {
        if (privateKeyValid == null) {
            this.privateKeyValid = null;
        } else {
            this.privateKeyValid = (Date)(Date)privateKeyValid.clone();
        }
    }
    
    public void setSubjectPublicKeyAlgID(String oid) throws IOException {
        if (oid == null) {
            subjectPublicKeyAlgID = null;
        } else {
            subjectPublicKeyAlgID = new ObjectIdentifier(oid);
        }
    }
    
    public void setSubjectPublicKey(PublicKey key) {
        if (key == null) {
            subjectPublicKey = null;
            subjectPublicKeyBytes = null;
        } else {
            subjectPublicKey = key;
            subjectPublicKeyBytes = key.getEncoded();
        }
    }
    
    public void setSubjectPublicKey(byte[] key) throws IOException {
        if (key == null) {
            subjectPublicKey = null;
            subjectPublicKeyBytes = null;
        } else {
            subjectPublicKeyBytes = (byte[])(byte[])key.clone();
            subjectPublicKey = X509Key.parse(new DerValue(subjectPublicKeyBytes));
        }
    }
    
    public void setKeyUsage(boolean[] keyUsage) {
        if (keyUsage == null) {
            this.keyUsage = null;
        } else {
            this.keyUsage = (boolean[])(boolean[])keyUsage.clone();
        }
    }
    
    public void setExtendedKeyUsage(Set keyPurposeSet) throws IOException {
        if ((keyPurposeSet == null) || keyPurposeSet.isEmpty()) {
            this.keyPurposeSet = null;
            keyPurposeOIDSet = null;
        } else {
            this.keyPurposeSet = Collections.unmodifiableSet(new HashSet(keyPurposeSet));
            keyPurposeOIDSet = new HashSet();
            for (Iterator i$ = this.keyPurposeSet.iterator(); i$.hasNext(); ) {
                String s = (String)i$.next();
                {
                    keyPurposeOIDSet.add(new ObjectIdentifier(s));
                }
            }
        }
    }
    
    public void setMatchAllSubjectAltNames(boolean matchAllNames) {
        this.matchAllSubjectAltNames = matchAllNames;
    }
    
    public void setSubjectAlternativeNames(Collection names) throws IOException {
        if (names == null) {
            subjectAlternativeNames = null;
            subjectAlternativeGeneralNames = null;
        } else {
            if (names.isEmpty()) {
                subjectAlternativeNames = null;
                subjectAlternativeGeneralNames = null;
                return;
            }
            Set tempNames = cloneAndCheckNames(names);
            subjectAlternativeGeneralNames = parseNames(tempNames);
            subjectAlternativeNames = tempNames;
        }
    }
    
    public void addSubjectAlternativeName(int type, String name) throws IOException {
        addSubjectAlternativeNameInternal(type, name);
    }
    
    public void addSubjectAlternativeName(int type, byte[] name) throws IOException {
        addSubjectAlternativeNameInternal(type, name.clone());
    }
    
    private void addSubjectAlternativeNameInternal(int type, Object name) throws IOException {
        GeneralNameInterface tempName = makeGeneralNameInterface(type, name);
        if (subjectAlternativeNames == null) {
            subjectAlternativeNames = new HashSet();
        }
        if (subjectAlternativeGeneralNames == null) {
            subjectAlternativeGeneralNames = new HashSet();
        }
        List list = new ArrayList(2);
        list.add(Integer.valueOf(type));
        list.add(name);
        subjectAlternativeNames.add(list);
        subjectAlternativeGeneralNames.add(tempName);
    }
    
    private static Set parseNames(Collection names) throws IOException {
        Set genNames = new HashSet();
        Iterator i = names.iterator();
        while (i.hasNext()) {
            Object o = i.next();
            if (!(o instanceof List)) {
                throw new IOException("expected List");
            }
            List nameList = (List)(List)o;
            if (nameList.size() != 2) {
                throw new IOException("name list size not 2");
            }
            o = nameList.get(0);
            if (!(o instanceof Integer)) {
                throw new IOException("expected an Integer");
            }
            int nameType = ((Integer)(Integer)o).intValue();
            o = nameList.get(1);
            genNames.add(makeGeneralNameInterface(nameType, o));
        }
        return genNames;
    }
    
    static boolean equalNames(Collection object1, Collection object2) {
        if ((object1 == null) || (object2 == null)) {
            return object1 == object2;
        }
        return object1.equals(object2);
    }
    
    static GeneralNameInterface makeGeneralNameInterface(int type, Object name) throws IOException {
        GeneralNameInterface result;
        if (debug != null) {
            debug.println("X509CertSelector.makeGeneralNameInterface(" + type + ")...");
        }
        if (name instanceof String) {
            if (debug != null) {
                debug.println("X509CertSelector.makeGeneralNameInterface() " + "name is String: " + name);
            }
            switch (type) {
            case NAME_RFC822: 
                result = new RFC822Name((String)(String)name);
                break;
            
            case NAME_DNS: 
                result = new DNSName((String)(String)name);
                break;
            
            case NAME_DIRECTORY: 
                result = new X500Name((String)(String)name);
                break;
            
            case NAME_URI: 
                result = new URIName((String)(String)name);
                break;
            
            case NAME_IP: 
                result = new IPAddressName((String)(String)name);
                break;
            
            case NAME_OID: 
                result = new OIDName((String)(String)name);
                break;
            
            default: 
                throw new IOException("unable to parse String names of type " + type);
            
            }
            if (debug != null) {
                debug.println("X509CertSelector.makeGeneralNameInterface() " + "result: " + result.toString());
            }
        } else if (name instanceof byte[]) {
            DerValue val = new DerValue((byte[])(byte[])name);
            if (debug != null) {
                debug.println("X509CertSelector.makeGeneralNameInterface() is byte[]");
            }
            switch (type) {
            case NAME_ANY: 
                result = new OtherName(val);
                break;
            
            case NAME_RFC822: 
                result = new RFC822Name(val);
                break;
            
            case NAME_DNS: 
                result = new DNSName(val);
                break;
            
            case NAME_X400: 
                result = new X400Address(val);
                break;
            
            case NAME_DIRECTORY: 
                result = new X500Name(val);
                break;
            
            case NAME_EDI: 
                result = new EDIPartyName(val);
                break;
            
            case NAME_URI: 
                result = new URIName(val);
                break;
            
            case NAME_IP: 
                result = new IPAddressName(val);
                break;
            
            case NAME_OID: 
                result = new OIDName(val);
                break;
            
            default: 
                throw new IOException("unable to parse byte array names of " + "type " + type);
            
            }
            if (debug != null) {
                debug.println("X509CertSelector.makeGeneralNameInterface() result: " + result.toString());
            }
        } else {
            if (debug != null) {
                debug.println("X509CertSelector.makeGeneralName() input name not String or byte array");
            }
            throw new IOException("name not String or byte array");
        }
        return result;
    }
    
    public void setNameConstraints(byte[] bytes) throws IOException {
        if (bytes == null) {
            ncBytes = null;
            nc = null;
        } else {
            ncBytes = (byte[])(byte[])bytes.clone();
            nc = new NameConstraintsExtension(FALSE, bytes);
        }
    }
    
    public void setBasicConstraints(int minMaxPathLen) {
        if (minMaxPathLen < -2) {
            throw new IllegalArgumentException("basic constraints less than -2");
        }
        basicConstraints = minMaxPathLen;
    }
    
    public void setPolicy(Set certPolicySet) throws IOException {
        if (certPolicySet == null) {
            policySet = null;
            policy = null;
        } else {
            Set tempSet = Collections.unmodifiableSet(new HashSet(certPolicySet));
            Iterator i = tempSet.iterator();
            Vector polIdVector = new Vector();
            while (i.hasNext()) {
                Object o = i.next();
                if (!(o instanceof String)) {
                    throw new IOException("non String in certPolicySet");
                }
                polIdVector.add(new CertificatePolicyId(new ObjectIdentifier((String)(String)o)));
            }
            policySet = tempSet;
            policy = new CertificatePolicySet(polIdVector);
        }
    }
    
    public void setPathToNames(Collection names) throws IOException {
        if ((names == null) || names.isEmpty()) {
            pathToNames = null;
            pathToGeneralNames = null;
        } else {
            Set tempNames = cloneAndCheckNames(names);
            pathToGeneralNames = parseNames(tempNames);
            pathToNames = tempNames;
        }
    }
    
    void setPathToNamesInternal(Set names) {
        pathToNames = Collections.<List<?>>emptySet();
        pathToGeneralNames = names;
    }
    
    public void addPathToName(int type, String name) throws IOException {
        addPathToNameInternal(type, name);
    }
    
    public void addPathToName(int type, byte[] name) throws IOException {
        addPathToNameInternal(type, name.clone());
    }
    
    private void addPathToNameInternal(int type, Object name) throws IOException {
        GeneralNameInterface tempName = makeGeneralNameInterface(type, name);
        if (pathToGeneralNames == null) {
            pathToNames = new HashSet();
            pathToGeneralNames = new HashSet();
        }
        List list = new ArrayList(2);
        list.add(Integer.valueOf(type));
        list.add(name);
        pathToNames.add(list);
        pathToGeneralNames.add(tempName);
    }
    
    public X509Certificate getCertificate() {
        return x509Cert;
    }
    
    public BigInteger getSerialNumber() {
        return serialNumber;
    }
    
    public X500Principal getIssuer() {
        return issuer;
    }
    
    public String getIssuerAsString() {
        return (issuer == null ? null : issuer.getName());
    }
    
    public byte[] getIssuerAsBytes() throws IOException {
        return (issuer == null ? null : issuer.getEncoded());
    }
    
    public X500Principal getSubject() {
        return subject;
    }
    
    public String getSubjectAsString() {
        return (subject == null ? null : subject.getName());
    }
    
    public byte[] getSubjectAsBytes() throws IOException {
        return (subject == null ? null : subject.getEncoded());
    }
    
    public byte[] getSubjectKeyIdentifier() {
        if (subjectKeyID == null) {
            return null;
        }
        return (byte[])(byte[])subjectKeyID.clone();
    }
    
    public byte[] getAuthorityKeyIdentifier() {
        if (authorityKeyID == null) {
            return null;
        }
        return (byte[])(byte[])authorityKeyID.clone();
    }
    
    public Date getCertificateValid() {
        if (certificateValid == null) {
            return null;
        }
        return (Date)(Date)certificateValid.clone();
    }
    
    public Date getPrivateKeyValid() {
        if (privateKeyValid == null) {
            return null;
        }
        return (Date)(Date)privateKeyValid.clone();
    }
    
    public String getSubjectPublicKeyAlgID() {
        if (subjectPublicKeyAlgID == null) {
            return null;
        }
        return subjectPublicKeyAlgID.toString();
    }
    
    public PublicKey getSubjectPublicKey() {
        return subjectPublicKey;
    }
    
    public boolean[] getKeyUsage() {
        if (keyUsage == null) {
            return null;
        }
        return (boolean[])(boolean[])keyUsage.clone();
    }
    
    public Set getExtendedKeyUsage() {
        return keyPurposeSet;
    }
    
    public boolean getMatchAllSubjectAltNames() {
        return matchAllSubjectAltNames;
    }
    
    public Collection getSubjectAlternativeNames() {
        if (subjectAlternativeNames == null) {
            return null;
        }
        return cloneNames(subjectAlternativeNames);
    }
    
    private static Set cloneNames(Collection names) {
        try {
            return cloneAndCheckNames(names);
        } catch (IOException e) {
            throw new RuntimeException("cloneNames encountered IOException: " + e.getMessage());
        }
    }
    
    private static Set cloneAndCheckNames(Collection names) throws IOException {
        Set namesCopy = new HashSet();
        Iterator i = names.iterator();
        while (i.hasNext()) {
            Object o = i.next();
            if (!(o instanceof List)) {
                throw new IOException("expected a List");
            }
            namesCopy.add(new ArrayList((List)(List)o));
        }
        i = namesCopy.iterator();
        while (i.hasNext()) {
            List nameList = (List)(List)i.next();
            if (nameList.size() != 2) {
                throw new IOException("name list size not 2");
            }
            Object o = nameList.get(0);
            if (!(o instanceof Integer)) {
                throw new IOException("expected an Integer");
            }
            int nameType = ((Integer)(Integer)o).intValue();
            if ((nameType < 0) || (nameType > 8)) {
                throw new IOException("name type not 0-8");
            }
            Object nameObject = nameList.get(1);
            if (!(nameObject instanceof byte[]) && !(nameObject instanceof String)) {
                if (debug != null) {
                    debug.println("X509CertSelector.cloneAndCheckNames() name not byte array");
                }
                throw new IOException("name not byte array or String");
            }
            if (nameObject instanceof byte[]) {
                nameList.set(1, ((byte[])(byte[])nameObject).clone());
            }
        }
        return namesCopy;
    }
    
    public byte[] getNameConstraints() {
        if (ncBytes == null) {
            return null;
        } else {
            return (byte[])(byte[])ncBytes.clone();
        }
    }
    
    public int getBasicConstraints() {
        return basicConstraints;
    }
    
    public Set getPolicy() {
        return policySet;
    }
    
    public Collection getPathToNames() {
        if (pathToNames == null) {
            return null;
        }
        return cloneNames(pathToNames);
    }
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("X509CertSelector: [\n");
        if (x509Cert != null) {
            sb.append("  Certificate: " + x509Cert.toString() + "\n");
        }
        if (serialNumber != null) {
            sb.append("  Serial Number: " + serialNumber.toString() + "\n");
        }
        if (issuer != null) {
            sb.append("  Issuer: " + getIssuerAsString() + "\n");
        }
        if (subject != null) {
            sb.append("  Subject: " + getSubjectAsString() + "\n");
        }
        sb.append("  matchAllSubjectAltNames flag: " + String.valueOf(matchAllSubjectAltNames) + "\n");
        if (subjectAlternativeNames != null) {
            sb.append("  SubjectAlternativeNames:\n");
            Iterator i = subjectAlternativeNames.iterator();
            while (i.hasNext()) {
                List list = (List)(List)i.next();
                sb.append("    type " + list.get(0) + ", name " + list.get(1) + "\n");
            }
        }
        if (subjectKeyID != null) {
            HexDumpEncoder enc = new HexDumpEncoder();
            sb.append("  Subject Key Identifier: " + enc.encodeBuffer(subjectKeyID) + "\n");
        }
        if (authorityKeyID != null) {
            HexDumpEncoder enc = new HexDumpEncoder();
            sb.append("  Authority Key Identifier: " + enc.encodeBuffer(authorityKeyID) + "\n");
        }
        if (certificateValid != null) {
            sb.append("  Certificate Valid: " + certificateValid.toString() + "\n");
        }
        if (privateKeyValid != null) {
            sb.append("  Private Key Valid: " + privateKeyValid.toString() + "\n");
        }
        if (subjectPublicKeyAlgID != null) {
            sb.append("  Subject Public Key AlgID: " + subjectPublicKeyAlgID.toString() + "\n");
        }
        if (subjectPublicKey != null) {
            sb.append("  Subject Public Key: " + subjectPublicKey.toString() + "\n");
        }
        if (keyUsage != null) {
            sb.append("  Key Usage: " + keyUsageToString(keyUsage) + "\n");
        }
        if (keyPurposeSet != null) {
            sb.append("  Extended Key Usage: " + keyPurposeSet.toString() + "\n");
        }
        if (policy != null) {
            sb.append("  Policy: " + policy.toString() + "\n");
        }
        if (pathToGeneralNames != null) {
            sb.append("  Path to names:\n");
            Iterator i = pathToGeneralNames.iterator();
            while (i.hasNext()) {
                sb.append("    " + i.next() + "\n");
            }
        }
        sb.append("]");
        return sb.toString();
    }
    
    private static String keyUsageToString(boolean[] k) {
        String s = "KeyUsage [\n";
        try {
            if (k[0]) {
                s += "  DigitalSignature\n";
            }
            if (k[1]) {
                s += "  Non_repudiation\n";
            }
            if (k[2]) {
                s += "  Key_Encipherment\n";
            }
            if (k[3]) {
                s += "  Data_Encipherment\n";
            }
            if (k[4]) {
                s += "  Key_Agreement\n";
            }
            if (k[5]) {
                s += "  Key_CertSign\n";
            }
            if (k[6]) {
                s += "  Crl_Sign\n";
            }
            if (k[7]) {
                s += "  Encipher_Only\n";
            }
            if (k[8]) {
                s += "  Decipher_Only\n";
            }
        } catch (ArrayIndexOutOfBoundsException ex) {
        }
        s += "]\n";
        return (s);
    }
    
    private static Extension getExtensionObject(X509Certificate cert, int extId) throws IOException {
        if (cert instanceof X509CertImpl) {
            X509CertImpl impl = (X509CertImpl)(X509CertImpl)cert;
            switch (extId) {
            case PRIVATE_KEY_USAGE_ID: 
                return impl.getPrivateKeyUsageExtension();
            
            case SUBJECT_ALT_NAME_ID: 
                return impl.getSubjectAlternativeNameExtension();
            
            case NAME_CONSTRAINTS_ID: 
                return impl.getNameConstraintsExtension();
            
            case CERT_POLICIES_ID: 
                return impl.getCertificatePoliciesExtension();
            
            case EXTENDED_KEY_USAGE_ID: 
                return impl.getExtendedKeyUsageExtension();
            
            default: 
                return null;
            
            }
        }
        byte[] rawExtVal = cert.getExtensionValue(EXTENSION_OIDS[extId]);
        if (rawExtVal == null) {
            return null;
        }
        DerInputStream in = new DerInputStream(rawExtVal);
        byte[] encoded = in.getOctetString();
        switch (extId) {
        case PRIVATE_KEY_USAGE_ID: 
            try {
                return new PrivateKeyUsageExtension(FALSE, encoded);
            } catch (CertificateException ex) {
                throw new IOException(ex.getMessage());
            }
        
        case SUBJECT_ALT_NAME_ID: 
            return new SubjectAlternativeNameExtension(FALSE, encoded);
        
        case NAME_CONSTRAINTS_ID: 
            return new NameConstraintsExtension(FALSE, encoded);
        
        case CERT_POLICIES_ID: 
            return new CertificatePoliciesExtension(FALSE, encoded);
        
        case EXTENDED_KEY_USAGE_ID: 
            return new ExtendedKeyUsageExtension(FALSE, encoded);
        
        default: 
            return null;
        
        }
    }
    
    public boolean match(Certificate cert) {
        if (!(cert instanceof X509Certificate)) {
            return false;
        }
        X509Certificate xcert = (X509Certificate)(X509Certificate)cert;
        if (debug != null) {
            debug.println("X509CertSelector.match(SN: " + (xcert.getSerialNumber()).toString(16) + "\n  Issuer: " + xcert.getIssuerDN() + "\n  Subject: " + xcert.getSubjectDN() + ")");
        }
        if (x509Cert != null) {
            if (!x509Cert.equals(xcert)) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: certs don\'t match");
                }
                return false;
            }
        }
        if (serialNumber != null) {
            if (!serialNumber.equals(xcert.getSerialNumber())) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: serial numbers don\'t match");
                }
                return false;
            }
        }
        if (issuer != null) {
            if (!issuer.equals(xcert.getIssuerX500Principal())) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: issuer DNs don\'t match");
                }
                return false;
            }
        }
        if (subject != null) {
            if (!subject.equals(xcert.getSubjectX500Principal())) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: subject DNs don\'t match");
                }
                return false;
            }
        }
        if (certificateValid != null) {
            try {
                xcert.checkValidity(certificateValid);
            } catch (CertificateException e) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: certificate not within validity period");
                }
                return false;
            }
        }
        if (subjectPublicKeyBytes != null) {
            byte[] certKey = xcert.getPublicKey().getEncoded();
            if (!Arrays.equals(subjectPublicKeyBytes, certKey)) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: subject public keys don\'t match");
                }
                return false;
            }
        }
        boolean result = matchBasicConstraints(xcert) && matchKeyUsage(xcert) && matchExtendedKeyUsage(xcert) && matchSubjectKeyID(xcert) && matchAuthorityKeyID(xcert) && matchPrivateKeyValid(xcert) && matchSubjectPublicKeyAlgID(xcert) && matchPolicy(xcert) && matchSubjectAlternativeNames(xcert) && matchPathToNames(xcert) && matchNameConstraints(xcert);
        if (result && (debug != null)) {
            debug.println("X509CertSelector.match returning: true");
        }
        return result;
    }
    
    private boolean matchSubjectKeyID(X509Certificate xcert) {
        if (subjectKeyID == null) {
            return true;
        }
        try {
            byte[] extVal = xcert.getExtensionValue("2.5.29.14");
            if (extVal == null) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: no subject key ID extension");
                }
                return false;
            }
            DerInputStream in = new DerInputStream(extVal);
            byte[] certSubjectKeyID = in.getOctetString();
            if (certSubjectKeyID == null || !Arrays.equals(subjectKeyID, certSubjectKeyID)) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: subject key IDs don\'t match");
                }
                return false;
            }
        } catch (IOException ex) {
            if (debug != null) {
                debug.println("X509CertSelector.match: exception in subject key ID check");
            }
            return false;
        }
        return true;
    }
    
    private boolean matchAuthorityKeyID(X509Certificate xcert) {
        if (authorityKeyID == null) {
            return true;
        }
        try {
            byte[] extVal = xcert.getExtensionValue("2.5.29.35");
            if (extVal == null) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: no authority key ID extension");
                }
                return false;
            }
            DerInputStream in = new DerInputStream(extVal);
            byte[] certAuthKeyID = in.getOctetString();
            if (certAuthKeyID == null || !Arrays.equals(authorityKeyID, certAuthKeyID)) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: authority key IDs don\'t match");
                }
                return false;
            }
        } catch (IOException ex) {
            if (debug != null) {
                debug.println("X509CertSelector.match: exception in authority key ID check");
            }
            return false;
        }
        return true;
    }
    
    private boolean matchPrivateKeyValid(X509Certificate xcert) {
        if (privateKeyValid == null) {
            return true;
        }
        PrivateKeyUsageExtension ext = null;
        try {
            ext = (PrivateKeyUsageExtension)(PrivateKeyUsageExtension)getExtensionObject(xcert, PRIVATE_KEY_USAGE_ID);
            if (ext != null) {
                ext.valid(privateKeyValid);
            }
        } catch (CertificateExpiredException e1) {
            if (debug != null) {
                String time = "n/a";
                try {
                    Date notAfter = (Date)(Date)ext.get(PrivateKeyUsageExtension.NOT_AFTER);
                    time = notAfter.toString();
                } catch (CertificateException ex) {
                }
                debug.println("X509CertSelector.match: private key usage not " + "within validity date; ext.NOT_After: " + time + "; X509CertSelector: " + this.toString());
                e1.printStackTrace();
            }
            return false;
        } catch (CertificateNotYetValidException e2) {
            if (debug != null) {
                String time = "n/a";
                try {
                    Date notBefore = (Date)(Date)ext.get(PrivateKeyUsageExtension.NOT_BEFORE);
                    time = notBefore.toString();
                } catch (CertificateException ex) {
                }
                debug.println("X509CertSelector.match: private key usage not " + "within validity date; ext.NOT_BEFORE: " + time + "; X509CertSelector: " + this.toString());
                e2.printStackTrace();
            }
            return false;
        } catch (CertificateException e3) {
            if (debug != null) {
                debug.println("X509CertSelector.match: CertificateException " + "in private key usage check; X509CertSelector: " + this.toString());
                e3.printStackTrace();
            }
            return false;
        } catch (IOException e4) {
            if (debug != null) {
                debug.println("X509CertSelector.match: IOException in " + "private key usage check; X509CertSelector: " + this.toString());
                e4.printStackTrace();
            }
            return false;
        }
        return true;
    }
    
    private boolean matchSubjectPublicKeyAlgID(X509Certificate xcert) {
        if (subjectPublicKeyAlgID == null) {
            return true;
        }
        try {
            byte[] encodedKey = xcert.getPublicKey().getEncoded();
            DerValue val = new DerValue(encodedKey);
            if (val.tag != DerValue.tag_Sequence) {
                throw new IOException("invalid key format");
            }
            AlgorithmId algID = AlgorithmId.parse(val.data.getDerValue());
            if (debug != null) {
                debug.println("X509CertSelector.match: subjectPublicKeyAlgID = " + subjectPublicKeyAlgID + ", xcert subjectPublicKeyAlgID = " + algID.getOID());
            }
            if (!subjectPublicKeyAlgID.equals(algID.getOID())) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: subject public key alg IDs don\'t match");
                }
                return false;
            }
        } catch (IOException e5) {
            if (debug != null) {
                debug.println("X509CertSelector.match: IOException in subject public key algorithm OID check");
            }
            return false;
        }
        return true;
    }
    
    private boolean matchKeyUsage(X509Certificate xcert) {
        if (keyUsage == null) {
            return true;
        }
        boolean[] certKeyUsage = xcert.getKeyUsage();
        if (certKeyUsage != null) {
            for (int keyBit = 0; keyBit < keyUsage.length; keyBit++) {
                if (keyUsage[keyBit] && ((keyBit >= certKeyUsage.length) || !certKeyUsage[keyBit])) {
                    if (debug != null) {
                        debug.println("X509CertSelector.match: key usage bits don\'t match");
                    }
                    return false;
                }
            }
        }
        return true;
    }
    
    private boolean matchExtendedKeyUsage(X509Certificate xcert) {
        if ((keyPurposeSet == null) || keyPurposeSet.isEmpty()) {
            return true;
        }
        try {
            ExtendedKeyUsageExtension ext = (ExtendedKeyUsageExtension)(ExtendedKeyUsageExtension)getExtensionObject(xcert, EXTENDED_KEY_USAGE_ID);
            if (ext != null) {
                Vector certKeyPurposeVector = (Vector)(Vector)ext.get(ExtendedKeyUsageExtension.USAGES);
                if (!certKeyPurposeVector.contains(ANY_EXTENDED_KEY_USAGE) && !certKeyPurposeVector.containsAll(keyPurposeOIDSet)) {
                    if (debug != null) {
                        debug.println("X509CertSelector.match: cert failed extendedKeyUsage criterion");
                    }
                    return false;
                }
            }
        } catch (IOException ex) {
            if (debug != null) {
                debug.println("X509CertSelector.match: IOException in extended key usage check");
            }
            return false;
        }
        return true;
    }
    
    private boolean matchSubjectAlternativeNames(X509Certificate xcert) {
        if ((subjectAlternativeNames == null) || subjectAlternativeNames.isEmpty()) {
            return true;
        }
        try {
            SubjectAlternativeNameExtension sanExt = (SubjectAlternativeNameExtension)(SubjectAlternativeNameExtension)getExtensionObject(xcert, SUBJECT_ALT_NAME_ID);
            if (sanExt == null) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: no subject alternative name extension");
                }
                return false;
            }
            GeneralNames certNames = (GeneralNames)(GeneralNames)sanExt.get(SubjectAlternativeNameExtension.SUBJECT_NAME);
            Iterator i = subjectAlternativeGeneralNames.iterator();
            while (i.hasNext()) {
                GeneralNameInterface matchName = (GeneralNameInterface)(GeneralNameInterface)i.next();
                boolean found = false;
                for (Iterator t = certNames.iterator(); t.hasNext() && !found; ) {
                    GeneralNameInterface certName = ((GeneralName)(GeneralName)t.next()).getName();
                    found = certName.equals(matchName);
                }
                if (!found && (matchAllSubjectAltNames || !i.hasNext())) {
                    if (debug != null) {
                        debug.println("X509CertSelector.match: subject alternative " + "name " + matchName + " not found");
                    }
                    return false;
                } else if (found && !matchAllSubjectAltNames) {
                    break;
                }
            }
        } catch (IOException ex) {
            if (debug != null) debug.println("X509CertSelector.match: IOException in subject alternative name check");
            return false;
        }
        return true;
    }
    
    private boolean matchNameConstraints(X509Certificate xcert) {
        if (nc == null) {
            return true;
        }
        try {
            if (!nc.verify(xcert)) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: name constraints not satisfied");
                }
                return false;
            }
        } catch (IOException e) {
            if (debug != null) {
                debug.println("X509CertSelector.match: IOException in name constraints check");
            }
            return false;
        }
        return true;
    }
    
    private boolean matchPolicy(X509Certificate xcert) {
        if (policy == null) {
            return true;
        }
        try {
            CertificatePoliciesExtension ext = (CertificatePoliciesExtension)(CertificatePoliciesExtension)getExtensionObject(xcert, CERT_POLICIES_ID);
            if (ext == null) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: no certificate policy extension");
                }
                return false;
            }
            List policies = (List)(List)ext.get(CertificatePoliciesExtension.POLICIES);
            List policyIDs = new ArrayList(policies.size());
            for (Iterator i$ = policies.iterator(); i$.hasNext(); ) {
                PolicyInformation info = (PolicyInformation)i$.next();
                {
                    policyIDs.add(info.getPolicyIdentifier());
                }
            }
            if (policy != null) {
                boolean foundOne = false;
                if (policy.getCertPolicyIds().isEmpty()) {
                    if (policyIDs.isEmpty()) {
                        if (debug != null) {
                            debug.println("X509CertSelector.match: cert failed policyAny criterion");
                        }
                        return false;
                    }
                } else {
                    for (Iterator i$ = policy.getCertPolicyIds().iterator(); i$.hasNext(); ) {
                        CertificatePolicyId id = (CertificatePolicyId)i$.next();
                        {
                            if (policyIDs.contains(id)) {
                                foundOne = true;
                                break;
                            }
                        }
                    }
                    if (!foundOne) {
                        if (debug != null) {
                            debug.println("X509CertSelector.match: cert failed policyAny criterion");
                        }
                        return false;
                    }
                }
            }
        } catch (IOException ex) {
            if (debug != null) {
                debug.println("X509CertSelector.match: IOException in certificate policy ID check");
            }
            return false;
        }
        return true;
    }
    
    private boolean matchPathToNames(X509Certificate xcert) {
        if (pathToGeneralNames == null) {
            return true;
        }
        try {
            NameConstraintsExtension ext = (NameConstraintsExtension)(NameConstraintsExtension)getExtensionObject(xcert, NAME_CONSTRAINTS_ID);
            if (ext == null) {
                return true;
            }
            if ((debug != null) && debug.isOn("certpath")) {
                debug.println("X509CertSelector.match pathToNames:\n");
                Iterator i = pathToGeneralNames.iterator();
                while (i.hasNext()) {
                    debug.println("    " + i.next() + "\n");
                }
            }
            GeneralSubtrees permitted = (GeneralSubtrees)(GeneralSubtrees)ext.get(NameConstraintsExtension.PERMITTED_SUBTREES);
            GeneralSubtrees excluded = (GeneralSubtrees)(GeneralSubtrees)ext.get(NameConstraintsExtension.EXCLUDED_SUBTREES);
            if (excluded != null) {
                if (matchExcluded(excluded) == false) {
                    return false;
                }
            }
            if (permitted != null) {
                if (matchPermitted(permitted) == false) {
                    return false;
                }
            }
        } catch (IOException ex) {
            if (debug != null) {
                debug.println("X509CertSelector.match: IOException in name constraints check");
            }
            return false;
        }
        return true;
    }
    
    private boolean matchExcluded(GeneralSubtrees excluded) {
        for (Iterator t = excluded.iterator(); t.hasNext(); ) {
            GeneralSubtree tree = (GeneralSubtree)(GeneralSubtree)t.next();
            GeneralNameInterface excludedName = tree.getName().getName();
            Iterator i = pathToGeneralNames.iterator();
            while (i.hasNext()) {
                GeneralNameInterface pathToName = (GeneralNameInterface)(GeneralNameInterface)i.next();
                if (excludedName.getType() == pathToName.getType()) {
                    switch (pathToName.constrains(excludedName)) {
                    case GeneralNameInterface.NAME_WIDENS: 
                    
                    case GeneralNameInterface.NAME_MATCH: 
                        if (debug != null) {
                            debug.println("X509CertSelector.match: name constraints inhibit path to specified name");
                            debug.println("X509CertSelector.match: excluded name: " + pathToName);
                        }
                        return false;
                    
                    default: 
                    
                    }
                }
            }
        }
        return true;
    }
    
    private boolean matchPermitted(GeneralSubtrees permitted) {
        Iterator i = pathToGeneralNames.iterator();
        while (i.hasNext()) {
            GeneralNameInterface pathToName = (GeneralNameInterface)(GeneralNameInterface)i.next();
            Iterator t = permitted.iterator();
            boolean permittedNameFound = false;
            boolean nameTypeFound = false;
            String names = "";
            while (t.hasNext() && !permittedNameFound) {
                GeneralSubtree tree = (GeneralSubtree)(GeneralSubtree)t.next();
                GeneralNameInterface permittedName = tree.getName().getName();
                if (permittedName.getType() == pathToName.getType()) {
                    nameTypeFound = true;
                    names = names + "  " + permittedName;
                    switch (pathToName.constrains(permittedName)) {
                    case GeneralNameInterface.NAME_WIDENS: 
                    
                    case GeneralNameInterface.NAME_MATCH: 
                        permittedNameFound = true;
                        break;
                    
                    default: 
                    
                    }
                }
            }
            if (!permittedNameFound && nameTypeFound) {
                if (debug != null) debug.println("X509CertSelector.match: " + "name constraints inhibit path to specified name; " + "permitted names of type " + pathToName.getType() + ": " + names);
                return false;
            }
        }
        return true;
    }
    
    private boolean matchBasicConstraints(X509Certificate xcert) {
        if (basicConstraints == -1) {
            return true;
        }
        int maxPathLen = xcert.getBasicConstraints();
        if (basicConstraints == -2) {
            if (maxPathLen != -1) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: not an EE cert");
                }
                return false;
            }
        } else {
            if (maxPathLen < basicConstraints) {
                if (debug != null) {
                    debug.println("X509CertSelector.match: maxPathLen too small (" + maxPathLen + " < " + basicConstraints + ")");
                }
                return false;
            }
        }
        return true;
    }
    
    private static Set cloneSet(Set set) {
        if (set instanceof HashSet) {
            Object clone = ((HashSet)(HashSet)set).clone();
            return (Set)(Set)clone;
        } else {
            return new HashSet(set);
        }
    }
    
    public Object clone() {
        try {
            X509CertSelector copy = (X509CertSelector)(X509CertSelector)super.clone();
            if (subjectAlternativeNames != null) {
                copy.subjectAlternativeNames = (Set)cloneSet(subjectAlternativeNames);
                copy.subjectAlternativeGeneralNames = (Set)cloneSet(subjectAlternativeGeneralNames);
            }
            if (pathToGeneralNames != null) {
                copy.pathToNames = (Set)cloneSet(pathToNames);
                copy.pathToGeneralNames = (Set)cloneSet(pathToGeneralNames);
            }
            return copy;
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e.toString());
        }
    }
}
