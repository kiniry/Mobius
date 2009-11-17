package java.lang;

import java.lang.reflect.Modifier;
import sun.reflect.annotation.*;

class Class$2 implements java.security.PrivilegedAction {
    /*synthetic*/ final Class this$0;
    
    Class$2(/*synthetic*/ final Class this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        java.util.List list = new java.util.ArrayList();
        Class currentClass = this$0;
        while (currentClass != null) {
            Class[] members = currentClass.getDeclaredClasses();
            for (int i = 0; i < members.length; i++) {
                if (Modifier.isPublic(members[i].getModifiers())) {
                    list.add(members[i]);
                }
            }
            currentClass = currentClass.getSuperclass();
        }
        Class[] empty = {};
        return list.toArray(empty);
    }
}
