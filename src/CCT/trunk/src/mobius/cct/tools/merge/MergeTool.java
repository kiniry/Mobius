package mobius.cct.tools.merge;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;

import mobius.cct.certificates.CertificateCollector;
import mobius.cct.certificates.DefaultCertificateParser;
import mobius.cct.certificates.writer.CertificateWriter;
import mobius.cct.classfile.DefaultClassFile;
import mobius.cct.classfile.DefaultClassReader;
import mobius.cct.tools.AbstractTool;
import mobius.cct.tools.Environment;
import mobius.cct.util.VisitorException;

/**
 * A tool which merges a certificate file with class.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MergeTool extends AbstractTool {
  /**
   * Expected number of arguments.
   */
  private static final int EXPECTED_ARGS = 4;
  
  /**
   * Position of input file name in argument list.
   */
  private static final int INPUT_ARG = 1;

  /**
   * Position of certificate file name in argument list.
   */
  private static final int CERT_ARG = 2;
  
  /**
   * Position of output file name in argument list.
   */
  private static final int OUTPUT_ARG = 3;
  
  /**
   * Read class file. Return null (and print a message) if
   * an error occurred. 
   * @param env Environment.
   * @return Parsed class file or null.
   * 
   */
  private DefaultClassFile readInput(final Environment env) {
    final PrintStream stderr = env.getErr();
    final DefaultClassReader reader = new DefaultClassReader();
    final String inputName = env.getArgs()[INPUT_ARG];
    try {
      return reader.read(new FileInputStream(inputName));
    } catch (FileNotFoundException e) {
      stderr.println(getMessage("merge.error.file.not.found", 
                                env, inputName));
      return null;
    } catch (IOException e) {
      stderr.println(getMessage("merge.error.ioexception", env));
      return null;
    }
  }

  /**
   * Read certificate file. Return null (and print a message) if
   * an error occurred. 
   * @param env Environment.
   * @return Parsed class file or null.
   */
  private DefaultClassFile readCerts(final Environment env) {
    final PrintStream stderr = env.getErr();
    final DefaultClassReader reader = new DefaultClassReader();
    final String certName = env.getArgs()[CERT_ARG];
    try {
      return reader.read(new FileInputStream(certName));
    } catch (FileNotFoundException e) {
      stderr.println(getMessage("merge.error.file.not.found", 
                                env, certName));
      return null;
    } catch (IOException e) {
      stderr.println(getMessage("merge.error.ioexception", env));
      return null;
    }
  }
  
  /**
   * Open output file. Return null in case of an error.
   * @param env Environment.
   * @return File output stream or null.
   * 
   */
  private FileOutputStream openOutput(final Environment env) {
    final PrintStream stderr = env.getErr();
    final String outputName = env.getArgs()[OUTPUT_ARG];
    try {
      return new FileOutputStream(outputName);
    } catch (FileNotFoundException e) {
      stderr.println(getMessage("merge.error.output.not.found", 
                                env, outputName));
      return null;
    }    
  }
  
  /**
   * Parse input files and write output.
   * @param input Input (class file).
   * @param cert Certificate file.
   * @param output Output stream.
   * @param env Environment.
   * @throws IOException 
   * 
   */
  private void extractCert(final DefaultClassFile input,
                           final DefaultClassFile cert,
                           final FileOutputStream output,
                           final Environment env) {
    final PrintStream stderr = env.getErr();
    
    final DefaultCertificateParser<DefaultClassFile> p = 
      new DefaultCertificateParser<DefaultClassFile>();
    final CertificateCollector<DefaultClassFile> col = 
      new CertificateCollector<DefaultClassFile>();
    final CertificateWriter writer = 
      new CertificateWriter(input, output);
    try {
      col.collect(p, input);
      col.collect(p, cert); 
      col.visitCertificates(writer, input.getName());
    } catch (IOException e) {
      stderr.println(getMessage("merge.error.ioexception", env));
    } catch (VisitorException e) {
      stderr.println(getMessage("merge.error.ioexception", env));
    }    
  }
  
  /**
   * Entry point.
   * @param env Environment.
   */
  public void main(final Environment env) {
    final PrintStream stderr = env.getErr();
    if (env.getArgs().length != EXPECTED_ARGS) {
      stderr.println(getMessage("tool.usage", env));
      return;
    }
    //
    final DefaultClassFile input = readInput(env);
    final DefaultClassFile cert = readCerts(env);
    if (input != null) {
      final FileOutputStream output = openOutput(env);
      if (output != null) {
        extractCert(input, cert, output, env);
      }
    }
  }

}
