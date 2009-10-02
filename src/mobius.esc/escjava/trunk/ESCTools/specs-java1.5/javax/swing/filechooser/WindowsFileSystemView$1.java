package javax.swing.filechooser;

import javax.swing.event.*;
import javax.swing.*;
import java.lang.reflect.*;
import sun.awt.shell.*;

class WindowsFileSystemView$1 extends FileSystemView$FileSystemRoot {
    /*synthetic*/ final WindowsFileSystemView this$0;
    
    WindowsFileSystemView$1(/*synthetic*/ final WindowsFileSystemView this$0, .java.io.File x0) {
        this.this$0 = this$0;
        super(x0);
    }
    
    public boolean exists() {
        return true;
    }
}
