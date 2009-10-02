package java.io;

import java.security.PrivilegedAction;

class ObjectStreamClass$2 implements PrivilegedAction {
    /*synthetic*/ final ObjectStreamClass this$0;
    /*synthetic*/ final Class val$cl;
    
    ObjectStreamClass$2(/*synthetic*/ final ObjectStreamClass this$0, /*synthetic*/ final Class val$cl) {
        this.this$0 = this$0;
        this.val$cl = val$cl;
        
    }
    
    public Object run() {
        if (ObjectStreamClass.access$400(this$0)) {
            ObjectStreamClass.access$502(this$0, new Long(0));
            ObjectStreamClass.access$602(this$0, ObjectStreamClass.NO_FIELDS);
            return null;
        }
        ObjectStreamClass.access$502(this$0, ObjectStreamClass.access$700(val$cl));
        try {
            ObjectStreamClass.access$602(this$0, ObjectStreamClass.access$800(val$cl));
            ObjectStreamClass.access$900(this$0);
        } catch (InvalidClassException e) {
            ObjectStreamClass.access$1002(this$0, ObjectStreamClass.access$1102(this$0, e));
            ObjectStreamClass.access$602(this$0, ObjectStreamClass.NO_FIELDS);
        }
        if (ObjectStreamClass.access$1200(this$0)) {
            ObjectStreamClass.access$1302(this$0, ObjectStreamClass.access$1400(val$cl));
        } else {
            ObjectStreamClass.access$1302(this$0, ObjectStreamClass.access$1500(val$cl));
            ObjectStreamClass.access$1602(this$0, ObjectStreamClass.access$1700(val$cl, "writeObject", new Class[]{ObjectOutputStream.class}, Void.TYPE));
            ObjectStreamClass.access$1802(this$0, ObjectStreamClass.access$1700(val$cl, "readObject", new Class[]{ObjectInputStream.class}, Void.TYPE));
            ObjectStreamClass.access$1902(this$0, ObjectStreamClass.access$1700(val$cl, "readObjectNoData", new Class[0], Void.TYPE));
            ObjectStreamClass.access$2002(this$0, (ObjectStreamClass.access$1600(this$0) != null));
        }
        ObjectStreamClass.access$2102(this$0, ObjectStreamClass.access$2200(val$cl, "writeReplace", new Class[0], Object.class));
        ObjectStreamClass.access$2302(this$0, ObjectStreamClass.access$2200(val$cl, "readResolve", new Class[0], Object.class));
        return null;
    }
}
