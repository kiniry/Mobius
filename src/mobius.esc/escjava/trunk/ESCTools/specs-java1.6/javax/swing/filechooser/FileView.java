package javax.swing.filechooser;

import java.io.File;
import javax.swing.*;

public abstract class FileView {
    
    public FileView() {
        
    }
    
    public String getName(File f) {
        return null;
    }
    {
    }
    
    public String getDescription(File f) {
        return null;
    }
    
    public String getTypeDescription(File f) {
        return null;
    }
    
    public Icon getIcon(File f) {
        return null;
    }
    
    public Boolean isTraversable(File f) {
        return null;
    }
}
