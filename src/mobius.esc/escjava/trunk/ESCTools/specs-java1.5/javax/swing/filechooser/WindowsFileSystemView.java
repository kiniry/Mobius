package javax.swing.filechooser;

import javax.swing.event.*;
import javax.swing.*;
import java.io.File;
import java.io.IOException;
import java.text.MessageFormat;
import java.lang.reflect.*;
import sun.awt.shell.*;

class WindowsFileSystemView extends FileSystemView {
    
    WindowsFileSystemView() {
        
    }
    private static final String newFolderString = UIManager.getString("FileChooser.win32.newFolder");
    private static final String newFolderNextString = UIManager.getString("FileChooser.win32.newFolder.subsequent");
    
    public Boolean isTraversable(File f) {
        return Boolean.valueOf(isFileSystemRoot(f) || isComputerNode(f) || f.isDirectory());
    }
    
    public File getChild(File parent, String fileName) {
        if (fileName.startsWith("\\") && !(fileName.startsWith("\\\\")) && isFileSystem(parent)) {
            String path = parent.getAbsolutePath();
            if (path.length() >= 2 && path.charAt(1) == ':' && Character.isLetter(path.charAt(0))) {
                return createFileObject(path.substring(0, 2) + fileName);
            }
        }
        return super.getChild(parent, fileName);
    }
    
    public String getSystemTypeDescription(File f) {
        if (f != null) {
            return getShellFolder(f).getFolderType();
        } else {
            return null;
        }
    }
    
    public File getHomeDirectory() {
        return getRoots()[0];
    }
    
    public File createNewFolder(File containingDir) throws IOException {
        if (containingDir == null) {
            throw new IOException("Containing directory is null:");
        }
        File newFolder = null;
        newFolder = createFileObject(containingDir, newFolderString);
        int i = 2;
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
    
    public boolean isDrive(File dir) {
        return isFileSystemRoot(dir);
    }
    
    public boolean isFloppyDrive(File dir) {
        String path = dir.getAbsolutePath();
        return (path != null && (path.equals("A:\\") || path.equals("B:\\")));
    }
    
    public File createFileObject(String path) {
        if (path.length() >= 2 && path.charAt(1) == ':' && Character.isLetter(path.charAt(0))) {
            if (path.length() == 2) {
                path += "\\";
            } else if (path.charAt(2) != '\\') {
                path = path.substring(0, 2) + "\\" + path.substring(2);
            }
        }
        return super.createFileObject(path);
    }
    
    protected File createFileSystemRoot(File f) {
        return new WindowsFileSystemView$1(this, f);
    }
}
