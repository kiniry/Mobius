package java.security.cert;

import java.util.Iterator;
import java.util.Set;

public interface PolicyNode {
    
    PolicyNode getParent();
    
    Iterator getChildren();
    
    int getDepth();
    
    String getValidPolicy();
    
    Set getPolicyQualifiers();
    
    Set getExpectedPolicies();
    
    boolean isCritical();
}
