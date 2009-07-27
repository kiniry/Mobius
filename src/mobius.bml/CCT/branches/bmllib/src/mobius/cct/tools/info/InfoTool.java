package mobius.cct.tools.info;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Iterator;

import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.ClassCertificateVisitor;
import mobius.cct.certificates.DefaultCertificateParser;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.certificates.MethodCertificateVisitor;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.DefaultClassFile;
import mobius.cct.classfile.DefaultClassReader;
import mobius.cct.classfile.MethodName;
import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.tools.AbstractTool;
import mobius.cct.tools.Environment;
import mobius.cct.util.VisitorException;

/**
 * A tool which prints various information about a 
 * class file.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class InfoTool extends AbstractTool {
  /**
   * Expected number of arguments.
   */
  private static final int EXPECTED_ARGS = 2;
  
  /**
   * Position of input file name in argument list.
   */
  private static final int INPUT_ARG = 1;
  
  /**
   * Read class file. Return null (and print a message) if
   * an error occurred. 
   * @param env Environment.
   * @return Parsed class file or null.
   */
  private DefaultClassFile readInput(final Environment env) {
    final PrintStream stderr = env.getErr();
    final DefaultClassReader reader = new DefaultClassReader();
    final String inputName = env.getArgs()[INPUT_ARG];
    try {
      return reader.read(new FileInputStream(inputName));
    } catch (FileNotFoundException e) {
      stderr.println(getMessage("info.error.file.not.found", 
                                env, inputName));
      return null;
    } catch (IOException e) {
      e.printStackTrace();
      stderr.println(getMessage("info.error.reading.input",
                                env, inputName));
      return null;
    }
  }
  
  /**
   * Print usage information.
   * @param env Environment.
   */
  private void printUsage(final Environment env) {
    final PrintStream stderr = env.getErr();
    stderr.println(getMessage("tool.usage", env));
  }
  
  /**
   * Print information about a class file.
   * @param f Class file.
   * @param env Environment.
   */
  private void printInfo(final DefaultClassFile f,
                         final Environment env) {
    final PrintStream stdout = env.getOutput();
    
    stdout.println(getMessage("info.class.major",
                              env,
                              f.getVersion().getMajor()));
    stdout.println(getMessage("info.class.minor",
                              env,
                              f.getVersion().getMinor()));
    stdout.println(getMessage("info.class.name",
                              env,
                              f.getName().externalForm()));
    final ClassName superName = f.getSuperName();
    if (superName != null) {
      stdout.println(getMessage("info.super.name",
                                env, superName.externalForm()));
    }
    
    final Iterator<ClassName> i = f.getInterfaces();
    if (i.hasNext()) {
      stdout.println(getMessage("info.class.interfaces", env));
      while (i.hasNext()) {
        stdout.println("> " + i.next().externalForm());
      }
    }
    printCerts(f, env);
  }

  /**
   * Print class certificates.
   * @param f Class file.
   * @param env Environment.
   */
  private void printCerts(final DefaultClassFile f,
                          final Environment env) {
    final PrintStream stderr = env.getErr();
    try {
      final DefaultCertificateParser<DefaultClassFile> p = 
        new DefaultCertificateParser<DefaultClassFile>();
      p.parse(f, new CertVisitor(env));
    } catch (VisitorException e) {
      stderr.println(getMessage("info.error.visit", env));
    } catch (InvalidFormatException e) {
      stderr.println(getMessage("info.error.format", env));
    }
  }
  
  /**
   * Entry point.
   * @param env Environment.
   */
  public void main(final Environment env) {
    if (env.getArgs().length != EXPECTED_ARGS) {
      printUsage(env);
      return;
    }
    final DefaultClassFile f = readInput(env);
    if (f != null) {
      printInfo(f, env);
    }
  }

  /**
   * A visitor used to print information about certificates 
   * of a class.
   * @author Tadeusz Sznuk (ts209501@gmail.com)
   */
  private final class CertVisitor 
    implements ClassCertificateVisitor {
    /**
     * Environment.
     */
    private final Environment fEnv;
    
    /**
     * Output stream.
     */
    private final PrintStream fOutput;
    
    /**
     * Constructor.
     * @param env Environment.
     */
    public CertVisitor(final Environment env) {
      fEnv = env;
      fOutput = env.getOutput();
    }
    
    /**
     * Print class name.
     * @param cls Class name.
     */
    public void begin(final ClassName cls) {
      fOutput.println(getMessage("info.certs.begin", 
                                 fEnv, 
                                 cls.externalForm()));
    }

    /**
     * end().
     */
    public void end() {
      fOutput.println(getMessage("info.certs.end", fEnv));
    }

    /**
     * Print information about a certificate.
     * @param cert Certificate.
     */
    public void visitClassCert(final ClassCertificate cert) {
      fOutput.println(getMessage("info.cert.begin", fEnv));
      fOutput.println(getMessage("info.cert.type", 
                                 fEnv, 
                                 cert.getType()));
      fOutput.println(getMessage("info.cert.major", 
                                 fEnv, 
                                 cert.getVersion().getMajor()));
      fOutput.println(getMessage("info.cert.minor", 
                                 fEnv, 
                                 cert.getVersion().getMinor()));

      if (cert.getImportCount() > 0) {
        fOutput.println(getMessage("info.cert.imports", fEnv));
        final Iterator<String> i = cert.getImports();
        while (i.hasNext()) {
          fOutput.println(">>> " + i.next());
        }
      }
      fOutput.println(getMessage("info.cert.end", fEnv));
    }

    /**
     * Print information about method certificates.
     * @param m Method name.
     * @return Method visitor.
     */
    public MethodCertificateVisitor 
    visitMethod(final MethodName m) {
      return new MethodCertVisitor();
    }
    
    /**
     * A visitor used to print information about 
     * method certificates.
     * @author Tadeusz Sznuk (ts209501@gmail.com)
     */
    private final class MethodCertVisitor
      implements MethodCertificateVisitor {

      /**
       * Print method name.
       * @param m Method name.
       */
      public void begin(final MethodName m) {
        fOutput.println(getMessage("info.method.name", 
                                   fEnv, 
                                   m.externalForm()));
      }

      /**
       * End().
       */
      public void end() {
        fOutput.println(getMessage("info.method.certs.end", fEnv));
      }

      /**
       * Print information about a method certificate.
       * @param cert Certificate.
       */
      public void visitMethodCert(final MethodCertificate cert) {
        fOutput.println(getMessage("info.method.cert.begin", fEnv));
        fOutput.println(getMessage("info.method.cert.type", 
                                   fEnv, 
                                   cert.getType()));
        fOutput.println(getMessage("info.method.cert.major", 
                                   fEnv, 
                                   cert.getVersion().getMajor()));
        fOutput.println(getMessage("info.method.cert.minor", 
                                   fEnv, 
                                   cert.getVersion().getMinor()));
        fOutput.println(getMessage("info.method.cert.end", fEnv));
      }
    }
  }
  
}
