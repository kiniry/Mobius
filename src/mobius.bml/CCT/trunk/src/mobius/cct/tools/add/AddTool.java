package mobius.cct.tools.add;

import java.io.ByteArrayOutputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

import mobius.cct.certificates.CertificateCollector;
import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.DefaultCertificateParser;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.certificates.writer.CertificateWriter;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.DefaultClassFile;
import mobius.cct.classfile.DefaultClassReader;
import mobius.cct.classfile.MethodName;
import mobius.cct.tools.AbstractTool;
import mobius.cct.tools.Environment;
import mobius.cct.util.Version;
import mobius.cct.util.VisitorException;

/**
 * A tool used to add class certificates to a file.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class AddTool extends AbstractTool {
  /**
   * Expected min number of arguments.
   */
  private static final int MIN_ARGS = 7;
  
  /**
   * Position of type (class or method) in argument list.
   */
  private static final int TYPE_ARG = 1;
  
  /**
   * Position of input file name in argument list.
   */
  private static final int INPUT_ARG = 2;

  /**
   * Position of output file name in argument list.
   */
  private static final int OUTPUT_ARG = 3;
  
  /**
   * Position of certificate type in argument list.
   */
  private static final int CERTTYPE_ARG = 4;
  
  /**
   * Position of major version number in argument list.
   */
  private static final int MAJOR_ARG = 5;
 
  /**
   * Position of minor version number in argument list.
   */
  private static final int MINOR_ARG = 6;
  
  /**
   * Position of first imported certificate name.
   */
  private static final int IMPORTS_ARG = 7;

  /**
   * Position of method name in argument list.
   */
  private static final int METHOD_ARG = 7;
  
  /**
   * Position of method type in argument list.
   */
  private static final int MTYPE_ARG = 8;
  
  /**
   * Size of buffers used to read stdin.
   */
  private static final int BUFFER_SIZE = 4096;
  
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
      stderr.println(getMessage("add.error.file.not.found", 
                                env, inputName));
      return null;
    } catch (IOException e) {
      stderr.println(getMessage("add.error.ioexception", env,
                                e.getMessage()));
      return null;
    }
  }
  
  /**
   * Collect certificates from a classfile.
   * @param f Class file.
   * @param env Environment.
   * @return Certificate packs.
   */
  private CertificateCollector<ClassFile> 
  getCertificates(final DefaultClassFile f, final Environment env) {
    final PrintStream stderr = env.getErr();
    final CertificateCollector<ClassFile> result = 
      new CertificateCollector<ClassFile>();
    final DefaultCertificateParser<ClassFile> parser = 
      new DefaultCertificateParser<ClassFile>();
    try {
      result.collect(parser, f);
      return result;
    } catch (IOException e) {
      stderr.println(getMessage("add.error.ioexception", 
                                env, e.getMessage()));
      return null;
    }
  }
  
  /**
   * Write certificates back to file.
   * @param f Class file.
   * @param o Output file.
   * @param c Modified certificates.
   * @param env Environment.
   */
  private void writeCerts(final DefaultClassFile f,
                          final OutputStream o,
                          final CertificateCollector<ClassFile> c,
                          final Environment env) {
    final PrintStream stderr = env.getErr();
    final CertificateWriter w = new CertificateWriter(f, o);
    try {
      c.visitCertificates(w, f.getName());
    } catch (VisitorException e) {
      stderr.println(getMessage("add.error.write", env));
    }
  }
  
  /**
   * Open output file. Return null in case of an error.
   * @param env Environment.
   * @return File output stream or null.
   */
  private FileOutputStream openOuput(final Environment env) {
    final PrintStream stderr = env.getErr();
    final String outputName = env.getArgs()[OUTPUT_ARG];
    try {
      return new FileOutputStream(outputName);
    } catch (FileNotFoundException e) {
      stderr.println(getMessage("add.error.output.not.found", 
                                env, outputName));
      return null;
    }    
  }
  
  /**
   * Read version number from args.
   * Return null (and print a message) if it is not valid.
   * @param env Environment.
   * @return Version or null.
   */
  private Version getVersion(final Environment env) {
    final String[] args = env.getArgs();
    final PrintStream stderr = env.getErr();
    
    final int major; 
    try {
      major = Integer.parseInt(args[MAJOR_ARG]);
      if ((major < 0) || (major > 0xff)) {
        throw new NumberFormatException();
      }
    } catch (NumberFormatException e) {
      stderr.println(getMessage("add.error.major.ver", 
                                env, args[MAJOR_ARG]));
      return null;
    }
    final int minor; 
    try {
      minor = Integer.parseInt(args[MINOR_ARG]);
      if ((minor < 0) || (minor > 255)) {
        throw new NumberFormatException();
      }
    } catch (NumberFormatException e) {
      stderr.println(getMessage("add.error.minor.ver", 
                                env, args[MINOR_ARG]));
      return null;
    }   
    return new Version(major, minor);
  }
  
  /**
   * Read imports from arguments.
   * @param env Environment.
   * @return Imports.
   */
  private String[] getImports(final Environment env) {
    final String[] args = env.getArgs();
    final int impcount = args.length - IMPORTS_ARG;
    final String[] imports = new String[impcount];
    for (int i = 0; i < impcount; i++) {
      imports[i] = args[IMPORTS_ARG + i];
    }
    return imports;
  }
  
  /**
   * Read certificate data from stdin.
   * If an error occurs, print a message and return null.
   * @param env Environment.
   * @return Certificate data or null.
   */
  private byte[] getData(final Environment env) {
    final PrintStream stderr = env.getErr();
    final InputStream stdin = env.getInput();
    int r;
    final ByteArrayOutputStream bos = new ByteArrayOutputStream();
    final byte[] buffer = new byte[BUFFER_SIZE];
    
    try {
      do {
        r = stdin.read(buffer);
        if (r > 0) {
          bos.write(buffer, 0, r);
        }
      } while (r > 0);
    } catch (IOException e) {
      stderr.println(getMessage("add.error.ioexception", env));
      return null;
    }
    return bos.toByteArray();
  }
  
  /**
   * Read arguments and construct the certificate.
   * @param env Environment.
   * @return Certificate.
   */
  private ClassCertificate createCert(final Environment env) {
    final String type = env.getArgs()[CERTTYPE_ARG];
    final Version version = getVersion(env);
    if (version == null) { return null; }
    final String[] imports = getImports(env);
    final byte[] data = getData(env);
    if (data == null) { return null; }
    return new ClassCertificate(type, version, imports, data);
  }

  /**
   * Read arguments and construct the method certificate.
   * @param env Environment.
   * @return Certificate.
   */
  private MethodCertificate createMCert(final Environment env) {
    final PrintStream stderr = env.getErr();
    if (env.getArgs().length <= MTYPE_ARG) {
      stderr.println(getMessage("tool.usage", env));
      return null;
    }
    final String type = env.getArgs()[CERTTYPE_ARG];
    final Version version = getVersion(env);
    if (version != null) {
  
      final String mn = env.getArgs()[METHOD_ARG];
      final String mt = env.getArgs()[MTYPE_ARG];
      final MethodName m = MethodName.get(mn, mt);
      if (m == null) {
        stderr.println(getMessage("add.error.method.name", env));
      } else {
        final byte[] data = getData(env);
        if (data != null) {
          return new MethodCertificate(m, type, version, data);
        }
      }
    }
    return null;
  }
  
  /**
   * Add new class certificate to existing certificates.
   * @param e Existing certificates.
   * @param n New certificate.
   */
  private void addCert(final CertificateCollector<ClassFile> e,
                       final ClassCertificate n) {
    final CertificatePack p = 
      e.getCertificatePack(n.getType(), n.getVersion());
    if (p == null) {
      e.addCertificates(
        new CertificatePack(n, new LinkedList<MethodCertificate>())
      );
    } else {
      e.removeCerts(n.getType(), n.getVersion());
      e.addCertificates(p.setClassCert(n));
    }
  }

  /**
   * Add new method certificate to existing certificates.
   * @param e Existing certificates.
   * @param n New certificate.
   */
  private void addMCert(final CertificateCollector<ClassFile> e,
                        final MethodCertificate n) {
    final CertificatePack p = 
      e.getCertificatePack(n.getType(), n.getVersion());
    if (p == null) {
      final ClassCertificate cc = new ClassCertificate(
        n.getType(), n.getVersion(), new String[]{}, new byte[]{}
      );
      final List<MethodCertificate> l = 
        new LinkedList<MethodCertificate>();
      l.add(n);
      e.addCertificates(new CertificatePack(cc, l));
    } else {
      e.addMethodCert(n);
    }
  }
  
  /**
   * Method called if addition of a class certificate was
   * requested.
   * @param env Environment.
   */
  public void addClassCertificate(final Environment env) {
    final ClassCertificate c = createCert(env);
    final DefaultClassFile f = readInput(env);
    if ((c != null) && (f != null)) {
      final CertificateCollector<ClassFile> certs = 
        getCertificates(f, env);
      if (certs != null) {
        addCert(certs, c);
        final FileOutputStream out = openOuput(env);
        if (out != null) {
          writeCerts(f, out, certs, env);
        }
      }
    }    
  }
  
  /**
   * Method called if addition of a method certificate was
   * requested.
   * @param env Environment.
   */
  public void addMethodCertificate(final Environment env) {
    final MethodCertificate c = createMCert(env);
    final DefaultClassFile f = readInput(env);
    if ((c != null) && (f != null)) {
      final CertificateCollector<ClassFile> certs = 
        getCertificates(f, env);
      if (certs != null) {
        addMCert(certs, c);
        final FileOutputStream out = openOuput(env);
        if (out != null) {
          writeCerts(f, out, certs, env);
        }
      }
    }    
  }
  
  /**
   * Entry point.
   * @param env Environment.
   */
  public void main(final Environment env) {
    final PrintStream stderr = env.getErr();
    if (env.getArgs().length < MIN_ARGS) {
      stderr.println(getMessage("tool.usage", env));
      return;
    }
    final String type = env.getArgs()[TYPE_ARG];
    if ("class".equalsIgnoreCase(type)) {
      addClassCertificate(env);
    } else if ("method".equalsIgnoreCase(type)) {
      addMethodCertificate(env);
    } else {
      stderr.println(
        getMessage("add.error.unknown.type", env, type)
      );
    }
  }

}
