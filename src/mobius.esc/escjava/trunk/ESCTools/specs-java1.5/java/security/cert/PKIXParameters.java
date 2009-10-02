package java.security.cert;

import java.security.InvalidAlgorithmParameterException;
import java.security.KeyStore;
import java.security.KeyStoreException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

public class PKIXParameters implements CertPathParameters {
    private Set unmodTrustAnchors;
    private Date date;
    private List certPathCheckers;
    private String sigProvider;
    private boolean revocationEnabled = true;
    private Set unmodInitialPolicies;
    private boolean explicitPolicyRequired = false;
    private boolean policyMappingInhibited = false;
    private boolean anyPolicyInhibited = false;
    private boolean policyQualifiersRejected = true;
    private List certStores;
    private CertSelector certSelector;
    
    public PKIXParameters(Set trustAnchors) throws InvalidAlgorithmParameterException {
        
        setTrustAnchors(trustAnchors);
        this.unmodInitialPolicies = Collections.<String>emptySet();
        this.certPathCheckers = new ArrayList();
        this.certStores = new ArrayList();
    }
    
    public PKIXParameters(KeyStore keystore) throws KeyStoreException, InvalidAlgorithmParameterException {
        
        if (keystore == null) throw new NullPointerException("the keystore parameter must be non-null");
        Set hashSet = new HashSet();
        Enumeration aliases = keystore.aliases();
        while (aliases.hasMoreElements()) {
            String alias = (String)(String)aliases.nextElement();
            if (keystore.isCertificateEntry(alias)) {
                Certificate cert = keystore.getCertificate(alias);
                if (cert instanceof X509Certificate) hashSet.add(new TrustAnchor((X509Certificate)(X509Certificate)cert, null));
            }
        }
        setTrustAnchors(hashSet);
        this.unmodInitialPolicies = Collections.<String>emptySet();
        this.certPathCheckers = new ArrayList();
        this.certStores = new ArrayList();
    }
    
    public Set getTrustAnchors() {
        return this.unmodTrustAnchors;
    }
    
    public void setTrustAnchors(Set trustAnchors) throws InvalidAlgorithmParameterException {
        if (trustAnchors == null) {
            throw new NullPointerException("the trustAnchors parameters must be non-null");
        }
        if (trustAnchors.isEmpty()) {
            throw new InvalidAlgorithmParameterException("the trustAnchors parameter must be non-empty");
        }
        for (Iterator i = trustAnchors.iterator(); i.hasNext(); ) {
            if (!(i.next() instanceof TrustAnchor)) {
                throw new ClassCastException("all elements of set must be of type java.security.cert.TrustAnchor");
            }
        }
        this.unmodTrustAnchors = Collections.unmodifiableSet(new HashSet(trustAnchors));
    }
    
    public Set getInitialPolicies() {
        return this.unmodInitialPolicies;
    }
    
    public void setInitialPolicies(Set initialPolicies) {
        if (initialPolicies != null) {
            for (Iterator i = initialPolicies.iterator(); i.hasNext(); ) {
                if (!(i.next() instanceof String)) throw new ClassCastException("all elements of set must be of type java.lang.String");
            }
            this.unmodInitialPolicies = Collections.unmodifiableSet(new HashSet(initialPolicies));
        } else this.unmodInitialPolicies = Collections.<String>emptySet();
    }
    
    public void setCertStores(List stores) {
        if (stores == null) {
            this.certStores = new ArrayList();
        } else {
            for (Iterator i = stores.iterator(); i.hasNext(); ) {
                if (!(i.next() instanceof CertStore)) {
                    throw new ClassCastException("all elements of list must be of type java.security.cert.CertStore");
                }
            }
            this.certStores = new ArrayList(stores);
        }
    }
    
    public void addCertStore(CertStore store) {
        if (store != null) {
            this.certStores.add(store);
        }
    }
    
    public List getCertStores() {
        return Collections.unmodifiableList(new ArrayList(this.certStores));
    }
    
    public void setRevocationEnabled(boolean val) {
        revocationEnabled = val;
    }
    
    public boolean isRevocationEnabled() {
        return revocationEnabled;
    }
    
    public void setExplicitPolicyRequired(boolean val) {
        explicitPolicyRequired = val;
    }
    
    public boolean isExplicitPolicyRequired() {
        return explicitPolicyRequired;
    }
    
    public void setPolicyMappingInhibited(boolean val) {
        policyMappingInhibited = val;
    }
    
    public boolean isPolicyMappingInhibited() {
        return policyMappingInhibited;
    }
    
    public void setAnyPolicyInhibited(boolean val) {
        anyPolicyInhibited = val;
    }
    
    public boolean isAnyPolicyInhibited() {
        return anyPolicyInhibited;
    }
    
    public void setPolicyQualifiersRejected(boolean qualifiersRejected) {
        policyQualifiersRejected = qualifiersRejected;
    }
    
    public boolean getPolicyQualifiersRejected() {
        return policyQualifiersRejected;
    }
    
    public Date getDate() {
        if (date == null) return null; else return (Date)(Date)this.date.clone();
    }
    
    public void setDate(Date date) {
        if (date != null) this.date = (Date)(Date)date.clone(); else date = null;
    }
    
    public void setCertPathCheckers(List checkers) {
        if (checkers != null) {
            List tmpList = new ArrayList();
            for (Iterator i$ = checkers.iterator(); i$.hasNext(); ) {
                PKIXCertPathChecker checker = (PKIXCertPathChecker)i$.next();
                {
                    tmpList.add((PKIXCertPathChecker)(PKIXCertPathChecker)checker.clone());
                }
            }
            this.certPathCheckers = tmpList;
        } else {
            this.certPathCheckers = new ArrayList();
        }
    }
    
    public List getCertPathCheckers() {
        List tmpList = new ArrayList();
        for (Iterator i$ = certPathCheckers.iterator(); i$.hasNext(); ) {
            PKIXCertPathChecker ck = (PKIXCertPathChecker)i$.next();
            {
                tmpList.add((PKIXCertPathChecker)(PKIXCertPathChecker)ck.clone());
            }
        }
        return Collections.unmodifiableList(tmpList);
    }
    
    public void addCertPathChecker(PKIXCertPathChecker checker) {
        if (checker != null) {
            certPathCheckers.add((PKIXCertPathChecker)(PKIXCertPathChecker)checker.clone());
        }
    }
    
    public String getSigProvider() {
        return this.sigProvider;
    }
    
    public void setSigProvider(String sigProvider) {
        this.sigProvider = sigProvider;
    }
    
    public CertSelector getTargetCertConstraints() {
        if (certSelector != null) {
            return (CertSelector)(CertSelector)certSelector.clone();
        } else {
            return null;
        }
    }
    
    public void setTargetCertConstraints(CertSelector selector) {
        if (selector != null) certSelector = (CertSelector)(CertSelector)selector.clone(); else certSelector = null;
    }
    
    public Object clone() {
        try {
            Object copy = super.clone();
            if (certStores != null) {
                certStores = new ArrayList(certStores);
            }
            if (certPathCheckers != null) {
                certPathCheckers = new ArrayList(certPathCheckers);
            }
            return copy;
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e.toString());
        }
    }
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("[\n");
        if (unmodTrustAnchors != null) {
            sb.append("  Trust Anchors: " + unmodTrustAnchors.toString() + "\n");
        }
        if (unmodInitialPolicies != null) {
            if (unmodInitialPolicies.isEmpty()) {
                sb.append("  Initial Policy OIDs: any\n");
            } else {
                sb.append("  Initial Policy OIDs: [" + unmodInitialPolicies.toString() + "]\n");
            }
        }
        sb.append("  Validity Date: " + String.valueOf(date) + "\n");
        sb.append("  Signature Provider: " + String.valueOf(sigProvider) + "\n");
        sb.append("  Default Revocation Enabled: " + revocationEnabled + "\n");
        sb.append("  Explicit Policy Required: " + explicitPolicyRequired + "\n");
        sb.append("  Policy Mapping Inhibited: " + policyMappingInhibited + "\n");
        sb.append("  Any Policy Inhibited: " + anyPolicyInhibited + "\n");
        sb.append("  Policy Qualifiers Rejected: " + policyQualifiersRejected + "\n");
        sb.append("  Target Cert Constraints: " + String.valueOf(certSelector) + "\n");
        if (certPathCheckers != null) sb.append("  Certification Path Checkers: [" + certPathCheckers.toString() + "]\n");
        if (certStores != null) sb.append("  CertStores: [" + certStores.toString() + "]\n");
        sb.append("]");
        return sb.toString();
    }
}
