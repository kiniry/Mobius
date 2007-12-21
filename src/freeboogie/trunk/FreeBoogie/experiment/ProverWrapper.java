import java.io.*;
import java.util.*;

class ProverError extends Exception {}

public class ProverWrapper {
  static ProcessBuilder pb;
  static Process p;
  static BufferedReader in;
  static PrintStream out;
  static boolean result;

  static char ch() throws ProverError {
    int c;
    try {
      c = in.read();
      if (c == -1) throw new ProverError();
      System.out.print((char)c);
    } catch (IOException e) {
      throw new ProverError();
    }
    return Character.toLowerCase((char) c);
  }

  static boolean processA() throws ProverError {
    char c = ch();
    if (Character.isLetterOrDigit(c)) {
      if (c == 'i') {
        result = false;
        return processC("nvalid");
      }
      if (c == 'v') {
        result = true;
        return processC("alid");
      }
      return processB();
    }
    return processA();
  }

  static boolean processB() throws ProverError {
    char c = ch();
    if (Character.isLetterOrDigit(c)) return processB();
    return processA();
  }

  static boolean processC(String expect) throws ProverError {
    int i;
    char c;
    for (i = 0; i < expect.length(); ++i) {
      if ((c = ch()) != expect.charAt(i)) {
        if (Character.isLetterOrDigit(c))
          return processB();
        else
          return processA();
      }
    }
    c = ch();
    if (Character.isLetterOrDigit(c)) return processB();
    if (c == '.') return result;
    return processE();
  }

  static boolean processE() throws ProverError {
    int cnt = 0;
    char c;
    while ((c = ch()) != '.' || cnt > 0) {
      if (c == '(') ++cnt; 
      if (c == ')') --cnt;
    }
    return result;
  }

  public static void main(String[] args) throws Exception {
    String[] z3 = {"z3","/si"};
    pb = new ProcessBuilder(Arrays.asList(z3));
    p = pb.start();
    in = new BufferedReader(new InputStreamReader(p.getInputStream()));
    out = new PrintStream(p.getOutputStream());

    for (String fn : args) {
      String line;
      BufferedReader br = new BufferedReader(new FileReader(fn));

      // Send one query
      while ((line = br.readLine()) != null) out.println(line);
      if (out.checkError()) {
        System.out.println("dbg> prover seems dead");
        break;
      }

      // Wait for \<Valid\>/\<Invalid\>, followed by a dot outside
      // parantheses.
      if (processA()) {
        System.out.println(fn + " is valid");
      } else {
        System.out.println(fn + " is invalid");
      }
    }
    out.close();
    p.waitFor();
    System.out.println("exit code " + p.exitValue()); 
  }
}
