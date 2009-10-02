package javax.sound.sampled;

public class AudioFileFormat$Type {
    public static final AudioFileFormat$Type WAVE = new AudioFileFormat$Type("WAVE", "wav");
    public static final AudioFileFormat$Type AU = new AudioFileFormat$Type("AU", "au");
    public static final AudioFileFormat$Type AIFF = new AudioFileFormat$Type("AIFF", "aif");
    public static final AudioFileFormat$Type AIFC = new AudioFileFormat$Type("AIFF-C", "aifc");
    public static final AudioFileFormat$Type SND = new AudioFileFormat$Type("SND", "snd");
    private final String name;
    private final String extension;
    
    public AudioFileFormat$Type(String name, String extension) {
        
        this.name = name;
        this.extension = extension;
    }
    
    public final boolean equals(Object obj) {
        if (toString() == null) {
            return (obj != null) && (obj.toString() == null);
        }
        if (obj instanceof AudioFileFormat$Type) {
            return toString().equals(obj.toString());
        }
        return false;
    }
    
    public final int hashCode() {
        if (toString() == null) {
            return 0;
        }
        return toString().hashCode();
    }
    
    public final String toString() {
        return name;
    }
    
    public String getExtension() {
        return extension;
    }
}
