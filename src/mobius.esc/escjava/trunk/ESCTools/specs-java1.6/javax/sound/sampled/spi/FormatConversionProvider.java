package javax.sound.sampled.spi;

import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;

public abstract class FormatConversionProvider {
    
    public FormatConversionProvider() {
        
    }
    
    public abstract AudioFormat$Encoding[] getSourceEncodings();
    
    public abstract AudioFormat$Encoding[] getTargetEncodings();
    
    public boolean isSourceEncodingSupported(AudioFormat$Encoding sourceEncoding) {
        AudioFormat$Encoding[] sourceEncodings = getSourceEncodings();
        for (int i = 0; i < sourceEncodings.length; i++) {
            if (sourceEncoding.equals(sourceEncodings[i])) {
                return true;
            }
        }
        return false;
    }
    
    public boolean isTargetEncodingSupported(AudioFormat$Encoding targetEncoding) {
        AudioFormat$Encoding[] targetEncodings = getTargetEncodings();
        for (int i = 0; i < targetEncodings.length; i++) {
            if (targetEncoding.equals(targetEncodings[i])) {
                return true;
            }
        }
        return false;
    }
    
    public abstract AudioFormat$Encoding[] getTargetEncodings(AudioFormat sourceFormat);
    
    public boolean isConversionSupported(AudioFormat$Encoding targetEncoding, AudioFormat sourceFormat) {
        AudioFormat$Encoding[] targetEncodings = getTargetEncodings(sourceFormat);
        for (int i = 0; i < targetEncodings.length; i++) {
            if (targetEncoding.equals(targetEncodings[i])) {
                return true;
            }
        }
        return false;
    }
    
    public abstract AudioFormat[] getTargetFormats(AudioFormat$Encoding targetEncoding, AudioFormat sourceFormat);
    
    public boolean isConversionSupported(AudioFormat targetFormat, AudioFormat sourceFormat) {
        AudioFormat[] targetFormats = getTargetFormats(targetFormat.getEncoding(), sourceFormat);
        for (int i = 0; i < targetFormats.length; i++) {
            if (targetFormat.matches(targetFormats[i])) {
                return true;
            }
        }
        return false;
    }
    
    public abstract AudioInputStream getAudioInputStream(AudioFormat$Encoding targetEncoding, AudioInputStream sourceStream);
    
    public abstract AudioInputStream getAudioInputStream(AudioFormat targetFormat, AudioInputStream sourceStream);
}
