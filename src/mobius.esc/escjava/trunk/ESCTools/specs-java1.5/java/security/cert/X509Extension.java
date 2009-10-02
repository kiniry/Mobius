package java.security.cert;

import java.util.Set;

public interface X509Extension {
    
    public boolean hasUnsupportedCriticalExtension();
    
    public Set getCriticalExtensionOIDs();
    
    public Set getNonCriticalExtensionOIDs();
    
    public byte[] getExtensionValue(String oid);
}
