package java.net;

import javax.net.ssl.SSLPeerUnverifiedException;
import java.security.Principal;
import java.util.List;

public abstract class SecureCacheResponse extends CacheResponse {
    
    public SecureCacheResponse() {
        
    }
    
    public abstract String getCipherSuite();
    
    public abstract List getLocalCertificateChain();
    
    public abstract List getServerCertificateChain() throws SSLPeerUnverifiedException;
    
    public abstract Principal getPeerPrincipal() throws SSLPeerUnverifiedException;
    
    public abstract Principal getLocalPrincipal();
}
