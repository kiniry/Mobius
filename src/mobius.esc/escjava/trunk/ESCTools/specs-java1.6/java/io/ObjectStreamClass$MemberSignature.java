package java.io;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Member;
import java.lang.reflect.Method;

class ObjectStreamClass$MemberSignature {
    public final Member member;
    public final String name;
    public final String signature;
    
    public ObjectStreamClass$MemberSignature(Field field) {
        
        member = field;
        name = field.getName();
        signature = ObjectStreamClass.getClassSignature(field.getType());
    }
    
    public ObjectStreamClass$MemberSignature(Constructor cons) {
        
        member = cons;
        name = cons.getName();
        signature = ObjectStreamClass.access$2400(cons.getParameterTypes(), Void.TYPE);
    }
    
    public ObjectStreamClass$MemberSignature(Method meth) {
        
        member = meth;
        name = meth.getName();
        signature = ObjectStreamClass.access$2400(meth.getParameterTypes(), meth.getReturnType());
    }
}
