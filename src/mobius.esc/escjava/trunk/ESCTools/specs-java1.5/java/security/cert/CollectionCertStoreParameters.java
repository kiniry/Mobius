package java.security.cert;

import java.util.Collection;
import java.util.Collections;

public class CollectionCertStoreParameters implements CertStoreParameters {
    private Collection coll;
    
    public CollectionCertStoreParameters(Collection collection) {
        
        if (collection == null) throw new NullPointerException();
        coll = collection;
    }
    
    public CollectionCertStoreParameters() {
        
        coll = Collections.EMPTY_SET;
    }
    
    public Collection getCollection() {
        return coll;
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e.toString());
        }
    }
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("CollectionCertStoreParameters: [\n");
        sb.append("  collection: " + coll + "\n");
        sb.append("]");
        return sb.toString();
    }
}
