package javax.sound.sampled;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

public class AudioFileFormat {
    private AudioFileFormat$Type type;
    private int byteLength;
    private AudioFormat format;
    private int frameLength;
    private HashMap properties;
    
    protected AudioFileFormat(AudioFileFormat$Type type, int byteLength, AudioFormat format, int frameLength) {
        
        this.type = type;
        this.byteLength = byteLength;
        this.format = format;
        this.frameLength = frameLength;
        this.properties = null;
    }
    
    public AudioFileFormat(AudioFileFormat$Type type, AudioFormat format, int frameLength) {
        this(type, AudioSystem.NOT_SPECIFIED, format, frameLength);
    }
    
    public AudioFileFormat(AudioFileFormat$Type type, AudioFormat format, int frameLength, Map properties) {
        this(type, AudioSystem.NOT_SPECIFIED, format, frameLength);
        this.properties = new HashMap(properties);
    }
    
    public AudioFileFormat$Type getType() {
        return type;
    }
    
    public int getByteLength() {
        return byteLength;
    }
    
    public AudioFormat getFormat() {
        return format;
    }
    
    public int getFrameLength() {
        return frameLength;
    }
    
    public Map properties() {
        Map ret;
        if (properties == null) {
            ret = new HashMap(0);
        } else {
            ret = (Map)((Map)properties.clone());
        }
        return (Map)Collections.unmodifiableMap(ret);
    }
    
    public Object getProperty(String key) {
        if (properties == null) {
            return null;
        }
        return properties.get(key);
    }
    
    public String toString() {
        StringBuffer buf = new StringBuffer();
        if (type != null) {
            buf.append(type.toString() + " (." + type.getExtension() + ") file");
        } else {
            buf.append("unknown file format");
        }
        if (byteLength != AudioSystem.NOT_SPECIFIED) {
            buf.append(", byte length: " + byteLength);
        }
        buf.append(", data format: " + format);
        if (frameLength != AudioSystem.NOT_SPECIFIED) {
            buf.append(", frame length: " + frameLength);
        }
        return new String(buf);
    }
    {
    }
}
