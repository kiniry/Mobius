package javax.sound.sampled.spi;

import javax.sound.sampled.Mixer;

public abstract class MixerProvider {
    
    public MixerProvider() {
        
    }
    
    public boolean isMixerSupported(Mixer$Info info) {
        Mixer$Info[] infos = getMixerInfo();
        for (int i = 0; i < infos.length; i++) {
            if (info.equals(infos[i])) {
                return true;
            }
        }
        return false;
    }
    
    public abstract Mixer$Info[] getMixerInfo();
    
    public abstract Mixer getMixer(Mixer$Info info);
}
