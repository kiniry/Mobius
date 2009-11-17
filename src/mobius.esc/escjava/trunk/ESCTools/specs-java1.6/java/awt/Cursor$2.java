package java.awt;

import java.io.FileInputStream;

class Cursor$2 implements java.security.PrivilegedExceptionAction {
    
    Cursor$2() throws java.io.IOException {
        
    }
    
    public Object run() throws Exception {
        FileInputStream fis = null;
        try {
            fis = new FileInputStream(Cursor.access$200());
            Cursor.access$300().load(fis);
        } finally {
            if (fis != null) fis.close();
        }
        return null;
    }
}
