package java.io;

import java.security.*;
import java.io.IOException;

class FilePermission$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final FilePermission this$0;
    
    FilePermission$1(/*synthetic*/ final FilePermission this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        try {
            File file = new File(FilePermission.access$000(this$0));
            String canonical_path = file.getCanonicalPath();
            int ln;
            if (FilePermission.access$100(this$0) && ((ln = canonical_path.length()) == 0 || canonical_path.charAt(ln - 1) != File.separatorChar)) {
                return canonical_path + File.separator;
            } else {
                return canonical_path;
            }
        } catch (IOException ioe) {
        }
        return FilePermission.access$000(this$0);
    }
}
