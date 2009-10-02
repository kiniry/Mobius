package javax.swing.filechooser;

import javax.swing.event.*;
import javax.swing.*;
import java.awt.Image;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Vector;
import java.lang.reflect.*;
import sun.awt.shell.*;

public abstract class FileSystemView {
    
    public FileSystemView() {
        
    }
    static FileSystemView windowsFileSystemView = null;
    static FileSystemView unixFileSystemView = null;
    static FileSystemView genericFileSystemView = null;
    static boolean useSystemExtensionsHiding = false;
    
    public static FileSystemView getFileSystemView() {
        useSystemExtensionsHiding = UIManager.getDefaults().getBoolean("FileChooser.useSystemExtensionHiding");
        UIManager.addPropertyChangeListener(new FileSystemView$1());
        if (File.separatorChar == '\\') {
            if (windowsFileSystemView == null) {
                windowsFileSystemView = new WindowsFileSystemView();
            }
            return windowsFileSystemView;
        }
        if (File.separatorChar == '/') {
            if (unixFileSystemView == null) {
                unixFileSystemView = new UnixFileSystemView();
            }
            return unixFileSystemView;
        }
        if (genericFileSystemView == null) {
            genericFileSystemView = new GenericFileSystemView();
        }
        return genericFileSystemView;
    }
    
    public boolean isRoot(File f) {
        if (f == null || !f.isAbsolute()) {
            return false;
        }
        File[] roots = getRoots();
        for (int i = 0; i < roots.length; i++) {
            if (roots[i].equals(f)) {
                return true;
            }
        }
        return false;
    }
    
    public Boolean isTraversable(File f) {
        return Boolean.valueOf(f.isDirectory());
    }
    
    public String getSystemDisplayName(File f) {
        String name = null;
        if (f != null) {
            name = f.getName();
            if (!name.equals("..") && !name.equals(".") && (useSystemExtensionsHiding || !isFileSystem(f) || isFileSystemRoot(f)) && ((f instanceof ShellFolder) || f.exists())) {
                name = getShellFolder(f).getDisplayName();
                if (name == null || name.length() == 0) {
                    name = f.getPath();
                }
            }
        }
        return name;
    }
    
    public String getSystemTypeDescription(File f) {
        return null;
    }
    
    public Icon getSystemIcon(File f) {
        if (f != null) {
            ShellFolder sf = getShellFolder(f);
            Image img = sf.getIcon(false);
            if (img != null) {
                return new ImageIcon(img, sf.getFolderType());
            } else {
                return UIManager.getIcon(f.isDirectory() ? "FileView.directoryIcon" : "FileView.fileIcon");
            }
        } else {
            return null;
        }
    }
    
    public boolean isParent(File folder, File file) {
        if (folder == null || file == null) {
            return false;
        } else if (folder instanceof ShellFolder) {
            File parent = file.getParentFile();
            if (parent != null && parent.equals(folder)) {
                return true;
            }
            File[] children = getFiles(folder, false);
            for (int i = 0; i < children.length; i++) {
                if (file.equals(children[i])) {
                    return true;
                }
            }
            return false;
        } else {
            return folder.equals(file.getParentFile());
        }
    }
    
    public File getChild(File parent, String fileName) {
        if (parent instanceof ShellFolder) {
            File[] children = getFiles(parent, false);
            for (int i = 0; i < children.length; i++) {
                if (children[i].getName().equals(fileName)) {
                    return children[i];
                }
            }
        }
        return createFileObject(parent, fileName);
    }
    
    public boolean isFileSystem(File f) {
        if (f instanceof ShellFolder) {
            ShellFolder sf = (ShellFolder)(ShellFolder)f;
            return sf.isFileSystem() && !(sf.isLink() && sf.isDirectory());
        } else {
            return true;
        }
    }
    
    public abstract File createNewFolder(File containingDir) throws IOException;
    
    public boolean isHiddenFile(File f) {
        return f.isHidden();
    }
    
    public boolean isFileSystemRoot(File dir) {
        return ShellFolder.isFileSystemRoot(dir);
    }
    
    public boolean isDrive(File dir) {
        return false;
    }
    
    public boolean isFloppyDrive(File dir) {
        return false;
    }
    
    public boolean isComputerNode(File dir) {
        return ShellFolder.isComputerNode(dir);
    }
    
    public File[] getRoots() {
        File[] roots = (File[])(File[])ShellFolder.get("roots");
        for (int i = 0; i < roots.length; i++) {
            if (isFileSystemRoot(roots[i])) {
                roots[i] = createFileSystemRoot(roots[i]);
            }
        }
        return roots;
    }
    
    public File getHomeDirectory() {
        return createFileObject(System.getProperty("user.home"));
    }
    
    public File getDefaultDirectory() {
        File f = (File)(File)ShellFolder.get("fileChooserDefaultFolder");
        if (isFileSystemRoot(f)) {
            f = createFileSystemRoot(f);
        }
        return f;
    }
    
    public File createFileObject(File dir, String filename) {
        if (dir == null) {
            return new File(filename);
        } else {
            return new File(dir, filename);
        }
    }
    
    public File createFileObject(String path) {
        File f = new File(path);
        if (isFileSystemRoot(f)) {
            f = createFileSystemRoot(f);
        }
        return f;
    }
    
    public File[] getFiles(File dir, boolean useFileHiding) {
        Vector files = new Vector();
        File[] names;
        if (!(dir instanceof ShellFolder)) {
            dir = getShellFolder(dir);
        }
        names = ((ShellFolder)(ShellFolder)dir).listFiles(!useFileHiding);
        File f;
        int nameCount = (names == null) ? 0 : names.length;
        for (int i = 0; i < nameCount; i++) {
            if (Thread.currentThread().isInterrupted()) {
                break;
            }
            f = names[i];
            if (!(f instanceof ShellFolder)) {
                if (isFileSystemRoot(f)) {
                    f = createFileSystemRoot(f);
                }
                try {
                    f = ShellFolder.getShellFolder(f);
                } catch (FileNotFoundException e) {
                    continue;
                } catch (InternalError e) {
                    continue;
                }
            }
            if (!useFileHiding || !isHiddenFile(f)) {
                files.addElement(f);
            }
        }
        return (File[])(File[])files.toArray(new File[files.size()]);
    }
    
    public File getParentDirectory(File dir) {
        if (dir != null && dir.exists()) {
            ShellFolder sf = getShellFolder(dir);
            File psf = sf.getParentFile();
            if (psf != null) {
                if (isFileSystem(psf)) {
                    File f = psf;
                    if (f != null && !f.exists()) {
                        File ppsf = psf.getParentFile();
                        if (ppsf == null || !isFileSystem(ppsf)) {
                            f = createFileSystemRoot(f);
                        }
                    }
                    return f;
                } else {
                    return psf;
                }
            }
        }
        return null;
    }
    
    ShellFolder getShellFolder(File f) {
        if (!(f instanceof ShellFolder) && !(f instanceof FileSystemView$FileSystemRoot) && isFileSystemRoot(f)) {
            f = createFileSystemRoot(f);
        }
        try {
            return ShellFolder.getShellFolder(f);
        } catch (FileNotFoundException e) {
            System.err.println("FileSystemView.getShellFolder: f=" + f);
            e.printStackTrace();
            return null;
        } catch (InternalError e) {
            System.err.println("FileSystemView.getShellFolder: f=" + f);
            e.printStackTrace();
            return null;
        }
    }
    
    protected File createFileSystemRoot(File f) {
        return new FileSystemView$FileSystemRoot(f);
    }
    {
    }
}
