package java.util.jar;

import java.util.SortedMap;
import java.io.InputStream;
import java.io.File;
import java.io.IOException;
import java.beans.PropertyChangeListener;

public interface Pack200$Unpacker {
    String KEEP = "keep";
    String TRUE = "true";
    String FALSE = "false";
    String DEFLATE_HINT = "unpack.deflate.hint";
    String PROGRESS = "unpack.progress";
    
    SortedMap properties();
    
    void unpack(InputStream in, JarOutputStream out) throws IOException;
    
    void unpack(File in, JarOutputStream out) throws IOException;
    
    void addPropertyChangeListener(PropertyChangeListener listener);
    
    void removePropertyChangeListener(PropertyChangeListener listener);
}
