package javax.sound.sampled;

public class AudioFormat$Encoding {
    public static final AudioFormat$Encoding PCM_SIGNED = new AudioFormat$Encoding("PCM_SIGNED");
    public static final AudioFormat$Encoding PCM_UNSIGNED = new AudioFormat$Encoding("PCM_UNSIGNED");
    public static final AudioFormat$Encoding ULAW = new AudioFormat$Encoding("ULAW");
    public static final AudioFormat$Encoding ALAW = new AudioFormat$Encoding("ALAW");
    private String name;
    
    public AudioFormat$Encoding(String name) {
        
        this.name = name;
    }
    
    public final boolean equals(Object obj) {
        if (toString() == null) {
            return (obj != null) && (obj.toString() == null);
        }
        if (obj instanceof AudioFormat$Encoding) {
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
}
