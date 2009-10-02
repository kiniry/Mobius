package java.lang.instrument;

import java.security.ProtectionDomain;

public interface ClassFileTransformer {
    
    byte[] transform(ClassLoader loader, String className, Class classBeingRedefined, ProtectionDomain protectionDomain, byte[] classfileBuffer) throws IllegalClassFormatException;
}
