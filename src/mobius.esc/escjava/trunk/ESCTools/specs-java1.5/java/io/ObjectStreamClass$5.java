package java.io;

import java.util.Comparator;

class ObjectStreamClass$5 implements Comparator {
    
    ObjectStreamClass$5() {
        
    }
    
    public int compare(Object o1, Object o2) {
        ObjectStreamClass$MemberSignature ms1 = (ObjectStreamClass$MemberSignature)(ObjectStreamClass$MemberSignature)o1;
        ObjectStreamClass$MemberSignature ms2 = (ObjectStreamClass$MemberSignature)(ObjectStreamClass$MemberSignature)o2;
        int comp = ms1.name.compareTo(ms2.name);
        if (comp == 0) {
            comp = ms1.signature.compareTo(ms2.signature);
        }
        return comp;
    }
}
