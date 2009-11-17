package javax.swing.plaf.basic;

import java.awt.event.*;
import java.io.*;
import java.util.*;
import java.lang.reflect.*;
import javax.sound.sampled.*;
import javax.swing.AbstractAction;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicLookAndFeel$AudioAction extends AbstractAction implements LineListener {
    /*synthetic*/ final BasicLookAndFeel this$0;
    private String audioResource;
    private byte[] audioBuffer;
    
    public BasicLookAndFeel$AudioAction(/*synthetic*/ final BasicLookAndFeel this$0, String name, String resource) {
        super(name);
        this.this$0 = this$0;
        audioResource = resource;
    }
    
    public void actionPerformed(ActionEvent e) {
        if (audioBuffer == null) {
            audioBuffer = BasicLookAndFeel.access$000(this$0, audioResource);
        }
        if (audioBuffer != null) {
            cancelCurrentSound(null);
            try {
                AudioInputStream soundStream = AudioSystem.getAudioInputStream(new ByteArrayInputStream(audioBuffer));
                DataLine$Info info = new DataLine$Info(Clip.class, soundStream.getFormat());
                Clip clip = (Clip)(Clip)AudioSystem.getLine(info);
                clip.open(soundStream);
                clip.addLineListener(this);
                synchronized (BasicLookAndFeel.access$100(this$0)) {
                    BasicLookAndFeel.access$202(this$0, clip);
                }
                clip.start();
            } catch (Exception ex) {
            }
        }
    }
    
    public void update(LineEvent event) {
        if (event.getType() == LineEvent$Type.STOP) {
            cancelCurrentSound((Clip)(Clip)event.getLine());
        }
    }
    
    private void cancelCurrentSound(Clip clip) {
        Clip lastClip = null;
        synchronized (BasicLookAndFeel.access$100(this$0)) {
            if (clip == null || clip == BasicLookAndFeel.access$200(this$0)) {
                lastClip = BasicLookAndFeel.access$200(this$0);
                BasicLookAndFeel.access$202(this$0, null);
            }
        }
        if (lastClip != null) {
            lastClip.removeLineListener(this);
            lastClip.close();
        }
    }
}
