package java.io;

import java.util.Comparator;

class ObjectStreamClass$4 implements Comparator {
    
    ObjectStreamClass$4() {
        
    }
    
    public int compare(Object o1, Object o2) {
        String sig1 = ((ObjectStreamClass$MemberSignature)(ObjectStreamClass$MemberSignature)o1).signature;
        String sig2 = ((ObjectStreamClass$MemberSignature)(ObjectStreamClass$MemberSignature)o2).signature;
        return sig1.compareTo(sig2);
    }
}
