package mobius.cct.tools.extract;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;

import mobius.cct.certificates.CertificateParser;
import mobius.cct.certificates.DefaultCertificateParser;
import mobius.cct.certificates.writer.CertificateFileWriter;
import mobius.cct.classfile.DefaultClassFile;
import mobius.cct.classfile.DefaultClassReader;
import mobius.cct.tools.AbstractTool;
import mobius.cct.tools.Environment;
import mobius.cct.util.VisitorException;

/**
 * A tool which extracts certificates from a class file.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class ExtractTool extends AbstractTool {
  /**
   * Expected number of arguments.
   */
  private static final int EXPECTED_ARGS = 3;
  
  /**
   * Position of input file name in argument list.
   */
  private static final int INPUT_ARG = 1;

  /**
   * Position of output file name in argument list.
   */
  private static final int OUTPUT_ARG = 2;
  
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
      stderr.println(getMessage("extract.error.file.not.found", 
                                env, inputName));
      return null;
    } catch (IOException e) {
      stderr.println(getMessage("extract.error.ioexception", env));
      return null;
    }
  }

  /**
   * Open output file. Return null in case of an error.
   * @param env Environment.
   * @return File output stream or null.
   */
  private FileOutputStream openOutput(final Environment env) {
    final PrintStream stderr = env.getErr();
    final String outputName = env.getArgs()[OUTPUT_ARG];
    try {
      return new FileOutputStream(outputName);
    } catch (FileNotFoundException e) {
      stderr.println(getMessage("extract.error.output.not.found", 
                                env, outputName));
      return null;
    }    
  }
  
  /**
   * Parse input file and write output.
   * @param input Input (class file).
   * @param output Output stream.
   * @param env Environment.
   * @throws IOException 
   */
  private void extractCert(final DefaultClassFile input,
                           final FileOutputStream output,
                           final Environment env) {
    final PrintStream stderr = env.getErr();
    final CertificateFileWriter writer = 
      new CertificateFileWriter(input.getName(), output);
    final CertificateParser<DefaultClassFile> p = 
      new DefaultCertificateParser<DefaultClassFile>();
    try {
      p.parse(input, writer);
      output.close();
    } catch (IOException e) {
      stderr.println(getMessage("extract.error.ioexception", env));
    } catch (VisitorException e) {
      stderr.println(getMessage("extract.error.ioexception", env));
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
    final DefaultClassFile input = readInput(env);
    if (input != null) {
      final FileOutputStream output = openOutput(env);
      if (output != null) {
        extractCert(input, output, env);
      }
    }
  }

}
