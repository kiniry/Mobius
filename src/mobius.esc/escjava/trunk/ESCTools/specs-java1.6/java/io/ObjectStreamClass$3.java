package java.io;

import java.util.Comparator;

class ObjectStreamClass$3 implements Comparator {
    
    ObjectStreamClass$3() {
        
    }
    
    public int compare(Object o1, Object o2) {
        String name1 = ((ObjectStreamClass$MemberSignature)(ObjectStreamClass$MemberSignature)o1).name;
        String name2 = ((ObjectStreamClass$MemberSignature)(ObjectStreamClass$MemberSignature)o2).name;
        return name1.compareTo(name2);
    }
}
