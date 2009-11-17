package java.util.jar;

import java.util.SortedMap;
import java.io.OutputStream;
import java.io.IOException;
import java.beans.PropertyChangeListener;

public interface Pack200$Packer {
    String SEGMENT_LIMIT = "pack.segment.limit";
    String KEEP_FILE_ORDER = "pack.keep.file.order";
    String EFFORT = "pack.effort";
    String DEFLATE_HINT = "pack.deflate.hint";
    String MODIFICATION_TIME = "pack.modification.time";
    String PASS_FILE_PFX = "pack.pass.file.";
    String UNKNOWN_ATTRIBUTE = "pack.unknown.attribute";
    String CLASS_ATTRIBUTE_PFX = "pack.class.attribute.";
    String FIELD_ATTRIBUTE_PFX = "pack.field.attribute.";
    String METHOD_ATTRIBUTE_PFX = "pack.method.attribute.";
    String CODE_ATTRIBUTE_PFX = "pack.code.attribute.";
    String PROGRESS = "pack.progress";
    String KEEP = "keep";
    String PASS = "pass";
    String STRIP = "strip";
    String ERROR = "error";
    String TRUE = "true";
    String FALSE = "false";
    String LATEST = "latest";
    
    SortedMap properties();
    
    void pack(JarFile in, OutputStream out) throws IOException;
    
    void pack(JarInputStream in, OutputStream out) throws IOException;
    
    void addPropertyChangeListener(PropertyChangeListener listener);
    
    void removePropertyChangeListener(PropertyChangeListener listener);
}
