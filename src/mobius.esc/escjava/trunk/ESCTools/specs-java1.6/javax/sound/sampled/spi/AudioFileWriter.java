package javax.sound.sampled.spi;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import javax.sound.sampled.AudioInputStream;

public abstract class AudioFileWriter {
    
    public AudioFileWriter() {
        
    }
    
    public abstract AudioFileFormat$Type[] getAudioFileTypes();
    
    public boolean isFileTypeSupported(AudioFileFormat$Type fileType) {
        AudioFileFormat$Type[] types = getAudioFileTypes();
        for (int i = 0; i < types.length; i++) {
            if (fileType.equals(types[i])) {
                return true;
            }
        }
        return false;
    }
    
    public abstract AudioFileFormat$Type[] getAudioFileTypes(AudioInputStream stream);
    
    public boolean isFileTypeSupported(AudioFileFormat$Type fileType, AudioInputStream stream) {
        AudioFileFormat$Type[] types = getAudioFileTypes(stream);
        for (int i = 0; i < types.length; i++) {
            if (fileType.equals(types[i])) {
                return true;
            }
        }
        return false;
    }
    
    public abstract int write(AudioInputStream stream, AudioFileFormat$Type fileType, OutputStream out) throws IOException;
    
    public abstract int write(AudioInputStream stream, AudioFileFormat$Type fileType, File out) throws IOException;
}
