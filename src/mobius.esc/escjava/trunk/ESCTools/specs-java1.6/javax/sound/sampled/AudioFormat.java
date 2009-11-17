package javax.sound.sampled;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

public class AudioFormat {
    protected AudioFormat$Encoding encoding;
    protected float sampleRate;
    protected int sampleSizeInBits;
    protected int channels;
    protected int frameSize;
    protected float frameRate;
    protected boolean bigEndian;
    private HashMap properties;
    
    public AudioFormat(AudioFormat$Encoding encoding, float sampleRate, int sampleSizeInBits, int channels, int frameSize, float frameRate, boolean bigEndian) {
        
        this.encoding = encoding;
        this.sampleRate = sampleRate;
        this.sampleSizeInBits = sampleSizeInBits;
        this.channels = channels;
        this.frameSize = frameSize;
        this.frameRate = frameRate;
        this.bigEndian = bigEndian;
        this.properties = null;
    }
    
    public AudioFormat(AudioFormat$Encoding encoding, float sampleRate, int sampleSizeInBits, int channels, int frameSize, float frameRate, boolean bigEndian, Map properties) {
        this(encoding, sampleRate, sampleSizeInBits, channels, frameSize, frameRate, bigEndian);
        this.properties = new HashMap(properties);
    }
    
    public AudioFormat(float sampleRate, int sampleSizeInBits, int channels, boolean signed, boolean bigEndian) {
        this((signed == true ? AudioFormat$Encoding.PCM_SIGNED : AudioFormat$Encoding.PCM_UNSIGNED), sampleRate, sampleSizeInBits, channels, (channels == AudioSystem.NOT_SPECIFIED || sampleSizeInBits == AudioSystem.NOT_SPECIFIED) ? AudioSystem.NOT_SPECIFIED : ((sampleSizeInBits + 7) / 8) * channels, sampleRate, bigEndian);
    }
    
    public AudioFormat$Encoding getEncoding() {
        return encoding;
    }
    
    public float getSampleRate() {
        return sampleRate;
    }
    
    public int getSampleSizeInBits() {
        return sampleSizeInBits;
    }
    
    public int getChannels() {
        return channels;
    }
    
    public int getFrameSize() {
        return frameSize;
    }
    
    public float getFrameRate() {
        return frameRate;
    }
    
    public boolean isBigEndian() {
        return bigEndian;
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
    
    public boolean matches(AudioFormat format) {
        if (format.getEncoding().equals(getEncoding()) && ((format.getSampleRate() == (float)AudioSystem.NOT_SPECIFIED) || (format.getSampleRate() == getSampleRate())) && (format.getSampleSizeInBits() == getSampleSizeInBits()) && (format.getChannels() == getChannels() && (format.getFrameSize() == getFrameSize()) && ((format.getFrameRate() == (float)AudioSystem.NOT_SPECIFIED) || (format.getFrameRate() == getFrameRate())) && ((format.getSampleSizeInBits() <= 8) || (format.isBigEndian() == isBigEndian())))) return true;
        return false;
    }
    
    public String toString() {
        String sEncoding = "";
        if (getEncoding() != null) {
            sEncoding = getEncoding().toString() + " ";
        }
        String sSampleRate;
        if (getSampleRate() == (float)AudioSystem.NOT_SPECIFIED) {
            sSampleRate = "unknown sample rate, ";
        } else {
            sSampleRate = "" + getSampleRate() + " Hz, ";
        }
        String sSampleSizeInBits;
        if (getSampleSizeInBits() == (float)AudioSystem.NOT_SPECIFIED) {
            sSampleSizeInBits = "unknown bits per sample, ";
        } else {
            sSampleSizeInBits = "" + getSampleSizeInBits() + " bit, ";
        }
        String sChannels;
        if (getChannels() == 1) {
            sChannels = "mono, ";
        } else if (getChannels() == 2) {
            sChannels = "stereo, ";
        } else {
            if (getChannels() == AudioSystem.NOT_SPECIFIED) {
                sChannels = " unknown number of channels, ";
            } else {
                sChannels = "" + getChannels() + " channels, ";
            }
        }
        String sFrameSize;
        if (getFrameSize() == (float)AudioSystem.NOT_SPECIFIED) {
            sFrameSize = "unknown frame size, ";
        } else {
            sFrameSize = "" + getFrameSize() + " bytes/frame, ";
        }
        String sFrameRate = "";
        if (Math.abs(getSampleRate() - getFrameRate()) > 1.0E-5) {
            if (getFrameRate() == (float)AudioSystem.NOT_SPECIFIED) {
                sFrameRate = "unknown frame rate, ";
            } else {
                sFrameRate = getFrameRate() + " frames/second, ";
            }
        }
        String sEndian = "";
        if ((getEncoding().equals(AudioFormat$Encoding.PCM_SIGNED) || getEncoding().equals(AudioFormat$Encoding.PCM_UNSIGNED)) && ((getSampleSizeInBits() > 8) || (getSampleSizeInBits() == AudioSystem.NOT_SPECIFIED))) {
            if (isBigEndian()) {
                sEndian = "big-endian";
            } else {
                sEndian = "little-endian";
            }
        }
        return sEncoding + sSampleRate + sSampleSizeInBits + sChannels + sFrameSize + sFrameRate + sEndian;
    }
    {
    }
}
