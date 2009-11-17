package java.util.zip;

import java.util.Enumeration;
import java.util.NoSuchElementException;
import java.lang.reflect.*;

class ZipFile$3 implements Enumeration {
    /*synthetic*/ final ZipFile this$0;
    
    ZipFile$3(/*synthetic*/ final ZipFile this$0) {
        this.this$0 = this$0;
        
    }
    private int i = 0;
    
    public boolean hasMoreElements() {
        synchronized (this$0) {
            ZipFile.access$400(this$0);
            return i < ZipFile.access$500(this$0);
        }
    }
    
    public ZipEntry nextElement() throws NoSuchElementException {
        synchronized (this$0) {
            ZipFile.access$400(this$0);
            if (i >= ZipFile.access$500(this$0)) {
                throw new NoSuchElementException();
            }
            long jzentry = ZipFile.access$700(ZipFile.access$600(this$0), i++);
            if (jzentry == 0) {
                String message;
                if (ZipFile.access$800(this$0)) {
                    message = "ZipFile concurrently closed";
                } else {
                    message = ZipFile.access$900(ZipFile.access$600(this$0));
                }
                throw new InternalError("jzentry == 0" + ",\n jzfile = " + ZipFile.access$600(this$0) + ",\n total = " + ZipFile.access$500(this$0) + ",\n name = " + ZipFile.access$1000(this$0) + ",\n i = " + i + ",\n message = " + message);
            }
            ZipEntry ze = new ZipEntry(jzentry);
            ZipFile.access$1100(ZipFile.access$600(this$0), jzentry);
            return ze;
        }
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
