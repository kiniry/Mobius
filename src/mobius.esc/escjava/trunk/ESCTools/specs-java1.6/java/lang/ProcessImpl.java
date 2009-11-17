package java.lang;

import java.io.IOException;
import java.lang.Process;

final class ProcessImpl {
    /*synthetic*/ static final boolean $assertionsDisabled = !ProcessImpl.class.desiredAssertionStatus();
    
    private ProcessImpl() {
        
    }
    
    private static byte[] toCString(String s) {
        if (s == null) return null;
        byte[] bytes = s.getBytes();
        byte[] result = new byte[bytes.length + 1];
        System.arraycopy(bytes, 0, result, 0, bytes.length);
        result[result.length - 1] = (byte)0;
        return result;
    }
    
    static Process start(String[] cmdarray, java.util.Map environment, String dir, boolean redirectErrorStream) throws IOException {
        if (!$assertionsDisabled && !(cmdarray != null && cmdarray.length > 0)) throw new AssertionError();
        byte[][] args = new byte[cmdarray.length - 1][];
        int size = args.length;
        for (int i = 0; i < args.length; i++) {
            args[i] = cmdarray[i + 1].getBytes();
            size += args[i].length;
        }
        byte[] argBlock = new byte[size];
        int i = 0;
        for (byte[][] arr$ = args, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            byte[] arg = arr$[i$];
            {
                System.arraycopy(arg, 0, argBlock, i, arg.length);
                i += arg.length + 1;
            }
        }
        int[] envc = new int[1];
        byte[] envBlock = ProcessEnvironment.toEnvironmentBlock(environment, envc);
        return new UNIXProcess(toCString(cmdarray[0]), argBlock, args.length, envBlock, envc[0], toCString(dir), redirectErrorStream);
    }
}
