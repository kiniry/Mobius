package javax.swing.filechooser;

import javax.swing.event.*;
import javax.swing.*;
import java.io.File;
import java.lang.reflect.*;
import sun.awt.shell.*;

class FileSystemView$FileSystemRoot extends File {
    
    public FileSystemView$FileSystemRoot(File f) {
        super(f, "");
    }
    
    public FileSystemView$FileSystemRoot(String s) {
        super(s);
    }
    
    public boolean isDirectory() {
        return true;
    }
    
    public String getName() {
        return getPath();
    }
}
