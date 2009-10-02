package java.security.cert;

import java.util.*;
import javax.security.auth.x500.X500Principal;
import sun.security.provider.certpath.CertPathHelper;

class CertPathHelperImpl extends CertPathHelper {
    
    private CertPathHelperImpl() {
        
    }
    
    static synchronized void initialize() {
        if (CertPathHelper.instance == null) {
            CertPathHelper.instance = new CertPathHelperImpl();
        }
    }
    
    protected void implSetSubject(X509CertSelector sel, X500Principal subject) {
        sel.setSubject(subject);
    }
    
    protected X500Principal implGetSubject(X509CertSelector sel) {
        return sel.getSubject();
    }
    
    protected void implSetIssuer(X509CertSelector sel, X500Principal issuer) {
        sel.setIssuer(issuer);
    }
    
    protected X500Principal implGetIssuer(X509CertSelector sel) {
        return sel.getIssuer();
    }
    
    protected X500Principal implGetCA(TrustAnchor anchor) {
        return anchor.getCA();
    }
    
    protected void implSetPathToNames(X509CertSelector sel, Set names) {
        sel.setPathToNamesInternal(names);
    }
    
    protected void implAddIssuer(X509CRLSelector sel, X500Principal name) {
        sel.addIssuer(name);
    }
    
    protected Collection implGetIssuers(X509CRLSelector sel) {
        return sel.getIssuers();
    }
}
