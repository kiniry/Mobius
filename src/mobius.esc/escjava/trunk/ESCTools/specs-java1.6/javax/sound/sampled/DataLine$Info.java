package javax.sound.sampled;

public class DataLine$Info extends Line$Info {
    private AudioFormat[] formats;
    private int minBufferSize;
    private int maxBufferSize;
    
    public DataLine$Info(Class lineClass, AudioFormat[] formats, int minBufferSize, int maxBufferSize) {
        super(lineClass);
        if (formats == null) {
            this.formats = new AudioFormat[0];
        } else {
            this.formats = formats;
        }
        this.minBufferSize = minBufferSize;
        this.maxBufferSize = maxBufferSize;
    }
    
    public DataLine$Info(Class lineClass, AudioFormat format, int bufferSize) {
        super(lineClass);
        if (format == null) {
            this.formats = new AudioFormat[0];
        } else {
            AudioFormat[] formats = {format};
            this.formats = formats;
        }
        this.minBufferSize = bufferSize;
        this.maxBufferSize = bufferSize;
    }
    
    public DataLine$Info(Class lineClass, AudioFormat format) {
        this(lineClass, format, AudioSystem.NOT_SPECIFIED);
    }
    
    public AudioFormat[] getFormats() {
        AudioFormat[] returnedArray = new AudioFormat[formats.length];
        System.arraycopy(formats, 0, returnedArray, 0, formats.length);
        return returnedArray;
    }
    
    public boolean isFormatSupported(AudioFormat format) {
        for (int i = 0; i < formats.length; i++) {
            if (format.matches(formats[i])) {
                return true;
            }
        }
        return false;
    }
    
    public int getMinBufferSize() {
        return minBufferSize;
    }
    
    public int getMaxBufferSize() {
        return maxBufferSize;
    }
    
    public boolean matches(Line$Info info) {
        if (!(super.matches(info))) {
            return false;
        }
        DataLine$Info dataLineInfo = (DataLine$Info)(DataLine$Info)info;
        if ((getMaxBufferSize() >= 0) && (dataLineInfo.getMaxBufferSize() >= 0)) {
            if (getMaxBufferSize() > dataLineInfo.getMaxBufferSize()) {
                return false;
            }
        }
        if ((getMinBufferSize() >= 0) && (dataLineInfo.getMinBufferSize() >= 0)) {
            if (getMinBufferSize() < dataLineInfo.getMinBufferSize()) {
                return false;
            }
        }
        AudioFormat[] localFormats = getFormats();
        if (localFormats != null) {
            for (int i = 0; i < localFormats.length; i++) {
                if (!(localFormats[i] == null)) {
                    if (!(dataLineInfo.isFormatSupported(localFormats[i]))) {
                        return false;
                    }
                }
            }
        }
        return true;
    }
    
    public String toString() {
        StringBuffer buf = new StringBuffer();
        if ((formats.length == 1) && (formats[0] != null)) {
            buf.append(" supporting format " + formats[0]);
        } else if (getFormats().length > 1) {
            buf.append(" supporting " + getFormats().length + " audio formats");
        }
        if ((minBufferSize != AudioSystem.NOT_SPECIFIED) && (maxBufferSize != AudioSystem.NOT_SPECIFIED)) {
            buf.append(", and buffers of " + minBufferSize + " to " + maxBufferSize + " bytes");
        } else if ((minBufferSize != AudioSystem.NOT_SPECIFIED) && (minBufferSize > 0)) {
            buf.append(", and buffers of at least " + minBufferSize + " bytes");
        } else if (maxBufferSize != AudioSystem.NOT_SPECIFIED) {
            buf.append(", and buffers of up to " + minBufferSize + " bytes");
        }
        return new String(super.toString() + buf);
    }
}
