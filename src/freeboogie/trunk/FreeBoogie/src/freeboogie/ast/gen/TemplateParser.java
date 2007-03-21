/** Public domain. */

package freeboogie.ast.gen;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Stack;
import java.util.logging.Logger;

import freeboogie.util.Err;

/**
 * TODO: description
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class TemplateParser {
  /*
   * TODO describe the implementation
   */

  private static final Logger log = Logger.getLogger("freeboogie.ast.gen");
  
  private TemplateLexer lexer;
  private Grammar grammar;
  
  private Stack<AgClass> classContext;
  private Stack<AgMember> memberContext;
  private Stack<AgEnum> enumContext;
  private Stack<String> valueContext;
  private Stack<String> invariantContext;
  
  private PrintStream output;
  
  /**
   * @param fileName the name of the template file
   * @throws FileNotFoundException if the template file is not found
   */
  public TemplateParser(String fileName) throws FileNotFoundException {
    FileInputStream fis = new FileInputStream(fileName);
    CharStream cs = new CharStream(fis, fileName);
    lexer = new TemplateLexer(cs);
    output = System.out;
  }

  /**
   * Processes the current template using grammar {@code g}.
   * @param g the grammar
   * @throws IOException 
   */
  public void process(Grammar g) throws IOException {
    grammar = g;
    processTop();
  }

  private void processTop() throws IOException {
    TemplateToken tok = lexer.next();
    while (tok != null) {
      switch (tok.type) {
      case FILE:
        processFile(); break;
      case CLASSES:
        processClasses(); break;
      case IS_ABSTRACT:
        processIsAbstract(); break;
      case ABSTRACT_CLASSES:
        processAbstractClasses(); break;
      case NORMAL_CLASSES:
        processNormalClasses(); break;
      case CLASS_NAME:
        processClassName(); break;
      case BASE_NAME:
        processBaseName(); break;
      case MEMBERS:
        processMembers(); break;
      case MEMBER_TYPE:
        processMemberType(); break;
      case MEMBER_NAME:
        processMemberName(); break;
      case IF_PRIMITIVE:
        processIfPrimitive(); break;
      case IF_NONNULL:
        processIfNonnull(); break;
      case CHILDREN:
        processChildren(); break;
      case PRIMITIVES:
        processPrimitives(); break;
      case ENUMS:
        processEnums(); break;
      case ENUM_NAME:
        processEnumName(); break;
      case VALUES:
        processValues(); break;
      case VALUE_NAME:
        processValueName(); break;
      case INVARIANTS:
        processInvariants(); break;
      case INV:
        processInv(); break;
      default:
        write(tok.rep);
      }
      lexer.eat();
      tok = lexer.next();
    }
  }
  
  /*
   * Reads { file_name } and makes output point to file_name.
   * If the file cannot be open then switch to a null output
   * and give a warning.
   */
  private void processFile() throws IOException {
    TemplateToken tok = lexer.next();
    if (tok.type != TemplateToken.Type.LC) {
      err("Hey, \\file should be followed by {");
      return; // TODO skip to } ?
    }
    tok = lexer.next();
    if (tok.type != TemplateToken.Type.OTHER) {
      err("Please don't use funny file names.");
      Err.help("macros can't be used in \file"); // TODO they MUST be usable!
      skipToRc();
      return;
    }
    try {
      output = new PrintStream(new FileOutputStream(tok.rep));
    } catch (Exception e) {
      err("Sorry, but I can't write to " + tok.rep);
    }
    Err.notImplemented();
  }
  
  private void processClasses() {
    Err.notImplemented();
  }
  
  private void processIsAbstract() {
    Err.notImplemented();
  }
  
  private void processAbstractClasses() {
    Err.notImplemented();
  }
  
  private void processNormalClasses() {
    Err.notImplemented();
  }
  
  private void processClassName() {
    Err.notImplemented();
  }
  
  private void processBaseName() {
    Err.notImplemented();
  }
  
  private void processMembers() {
    Err.notImplemented();
  }
  
  private void processMemberType() {
    Err.notImplemented();
  }
  
  private void processMemberName() {
    Err.notImplemented();
  }
  
  private void processIfPrimitive() {
    Err.notImplemented();
  }
  
  private void processIfNonnull() {
    Err.notImplemented();
  }
  
  private void processChildren() {
    Err.notImplemented();
  }
  
  private void processPrimitives() {
    Err.notImplemented();
  }
  
  private void processEnums() {
    Err.notImplemented();
  }
  
  private void processEnumName() {
    Err.notImplemented();
  }
  
  private void processValues() {
    Err.notImplemented();
  }
  
  private void processValueName() {
    Err.notImplemented();
  }
  
  private void processInvariants() {
    Err.notImplemented();
  }
  
  private void processInv() {
    Err.notImplemented();
  }
  
  private void skipToRc() {
    // TODO print warning?
    Err.notImplemented();
  }
  
  /*
   * Sends |s| to the |output|.
   */
  private void write(String s) {
    Err.notImplemented();
  }
  
  private void err(String e) {
    Err.error(lexer.getName() + lexer.getLoc() + ": " + e);
  }

  /**
   * TODO testing
   * @param args
   */
  public static void main(String[] args) {
    // TODO Auto-generated method stub
  }
}
