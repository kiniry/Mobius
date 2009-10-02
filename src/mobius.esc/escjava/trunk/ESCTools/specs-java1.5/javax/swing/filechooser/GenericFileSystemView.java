package javax.swing.filechooser;

import javax.swing.event.*;
import javax.swing.*;
import java.io.File;
import java.io.IOException;
import java.lang.reflect.*;
import sun.awt.shell.*;

class GenericFileSystemView extends FileSystemView {
    
    GenericFileSystemView() {
        
    }
    private static final String newFolderString = UIManager.getString("FileChooser.other.newFolder");
    
    public File createNewFolder(File containingDir) throws IOException {
        if (containingDir == null) {
            throw new IOException("Containing directory is null:");
        }
        File newFolder = null;
        newFolder = createFileObject(containingDir, newFolderString);
        if (newFolder.exists()) {
            throw new IOException("Directory already exists:" + newFolder.getAbsolutePath());
        } else {
            newFolder.mkdirs();
        }
        return newFolder;
    }
}
