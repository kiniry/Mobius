package javax.swing.filechooser;

import javax.swing.event.*;
import javax.swing.*;
import java.io.File;
import java.io.IOException;
import java.text.MessageFormat;
import java.lang.reflect.*;
import sun.awt.shell.*;

class UnixFileSystemView extends FileSystemView {
    
    UnixFileSystemView() {
        
    }
    private static final String newFolderString = UIManager.getString("FileChooser.other.newFolder");
    private static final String newFolderNextString = UIManager.getString("FileChooser.other.newFolder.subsequent");
    
    public File createNewFolder(File containingDir) throws IOException {
        if (containingDir == null) {
            throw new IOException("Containing directory is null:");
        }
        File newFolder = null;
        newFolder = createFileObject(containingDir, newFolderString);
        int i = 1;
        while (newFolder.exists() && (i < 100)) {
            newFolder = createFileObject(containingDir, MessageFormat.format(newFolderNextString, new Object[]{new Integer(i)}));
            i++;
        }
        if (newFolder.exists()) {
            throw new IOException("Directory already exists:" + newFolder.getAbsolutePath());
        } else {
            newFolder.mkdirs();
        }
        return newFolder;
    }
    
    public boolean isFileSystemRoot(File dir) {
        return (dir != null && dir.getAbsolutePath().equals("/"));
    }
    
    public boolean isDrive(File dir) {
        if (isFloppyDrive(dir)) {
            return true;
        } else {
            return false;
        }
    }
    
    public boolean isFloppyDrive(File dir) {
        return false;
    }
    
    public boolean isComputerNode(File dir) {
        if (dir != null) {
            String parent = dir.getParent();
            if (parent != null && parent.equals("/net")) {
                return true;
            }
        }
        return false;
    }
}
