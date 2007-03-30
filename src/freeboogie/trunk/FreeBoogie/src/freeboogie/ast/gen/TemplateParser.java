/** Public domain. */

package freeboogie.ast.gen;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Collection;
import java.util.Set;
import java.util.Stack;
import java.util.Map.Entry;
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
   * The function |processTop| is the main loop. It reads a
   * token and distributes the work to various |process*| methods.
   * It is also responsible for stopping when a certain closing
   * } or ] is met (and it reads it). The variables |curlyCnt|
   * and |bracketCnt| count the nesting (since the beginning
   * of the template) and are used to identify on which ] or }
   * we should stop. Notice that the user shouldn't use unbalanaced
   * paranthesis in the template for this scheme to work.
   * 
   * The stacks |*Context| contain information about the nested
   * macros seen in the input.
   */

  private static final Logger log = Logger.getLogger("freeboogie.ast.gen");
  
  private TemplateLexer lexer;
  private Grammar grammar;
  
  private Stack<AgClass> classContext;
  private Stack<AgMember> memberContext;
  private Stack<AgEnum> enumContext;
  private Stack<String> valueContext;
  private Stack<String> invariantContext;
  
  private Writer output;
  
  private int curlyCnt; // counts {} nesting
  private int bracketCnt; // counts [] nesting
  
  private TemplateToken lastToken;
  
  private boolean balancedWarning = true;
  
  /**
   * @param fileName the name of the template file
   * @throws FileNotFoundException if the template file is not found
   */
  public TemplateParser(String fileName) throws FileNotFoundException {
    FileInputStream fis = new FileInputStream(fileName);
    CharStream cs = new CharStream(fis, fileName);
    lexer = new TemplateLexer(cs);
    output = null;
    lastToken = null;
    
    classContext = new Stack<AgClass>();
    memberContext = new Stack<AgMember>();
    enumContext = new Stack<AgEnum>();
    valueContext = new Stack<String>();
    invariantContext = new Stack<String>();
  }

  /**
   * Processes the current template using grammar {@code g}.
   * @param g the grammar
   * @throws IOException 
   */
  public void process(Grammar g) throws IOException {
    grammar = g;
    processTop(Integer.MAX_VALUE, Integer.MAX_VALUE);
    output.flush();
  }

  /*
   * For now I will enforce {} and [] to be balanced pretty much 
   * everywhere.
   */
  private void processTop(int curlyStop, int bracketStop) throws IOException {
    readToken();
    while (lastToken != null) {
      switch (lastToken.type) {
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
        if (curlyStop == curlyCnt || bracketStop == bracketCnt) return;
        write(lastToken.rep);
      }
      if (curlyCnt == 0 && bracketCnt == 0) lexer.eat();
      readToken();
    }
  }
  
  /*
   * Reads { file_name } and makes output point to file_name.
   * If the file cannot be open then switch to a null output
   * and give a warning.
   */
  private void processFile() throws IOException {
    readToken();
    if (lastToken.type != TemplateToken.Type.LC) {
      err("Hey, \\file should be followed by {");
      Err.help("I'm gonna stop producing output.");
      switchOutput(null);
      return; // TODO skip to } ?
    }
    StringWriter sw = new StringWriter();
    switchOutput(sw);
    processTop(curlyCnt - 1, Integer.MAX_VALUE);
    String fn = sw.toString().replaceAll("\\s+", "_");
    try {
      FileWriter fw = new FileWriter(fn);
      switchOutput(fw);
      log.info("The output goes to the file " + fn);
    } catch (IOException e) {
      err("Cannot write to file " + fn);
      Err.help("I'm gonna stop producing output.");
      switchOutput(null);
    }
  }
  
  private <T> void processList(Collection<T> set, Stack<T> stack) throws IOException {
    readToken();
    String separator = "";
    if (lastToken.type == TemplateToken.Type.LB) {
      readToken();
      if (lastToken.type != TemplateToken.Type.OTHER) {
         err("Sorry, you can't use any funny stuff as a separator.");
        skipToRc(curlyCnt, true);
        return;
      }
      separator = lastToken.rep;
      readToken();
      if (lastToken.type != TemplateToken.Type.RB) {
        err("The separator is not properly closed by ].");
        skipToRb(bracketCnt - 1, true);
      }
      if (lastToken.type != TemplateToken.Type.LC)
        readToken();
    }
    if (lastToken.type != TemplateToken.Type.LC) {
      err("There should be a { after a list macro.");
      skipToRc(curlyCnt - 1, true);
      return;
    }
    if (set.isEmpty()) skipToRc(curlyCnt - 1, false);
    int i = 0; // TODO is there another way to check if I'm looking at the last?
    for (T el : set) {
      if (i != 0) {
        lexer.rewind();
        write(separator);
        ++curlyCnt;
      }
      if (++i != set.size()) lexer.mark();
        
      stack.add(el);
      processTop(curlyCnt - 1, Integer.MAX_VALUE);
      stack.pop();
    }
  }
  
  private void processClasses() throws IOException {
    processList(grammar.classes.values(), classContext);
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
  
  private void processClassName() throws IOException {
    if (classContext.isEmpty()) {
      err("You can only use \\class_name inside a macro that enumerates classes.");
      return;
    }
    writeId(classContext.peek().name, lastToken.idCase);
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
  
  private void skipToRc(int cnt, boolean warn) throws IOException {
    skipToR(cnt, Integer.MAX_VALUE, warn);
  }
  
  private void skipToRb(int cnt, boolean warn) throws IOException {
    skipToR(Integer.MAX_VALUE, cnt, warn);
  }
  
  /*
   * This reads the input until either it finishes or the } or ]
   * with the specified nesting level is encountered. 
   */
  private void skipToR(int curlyStop, int bracketStop, boolean w) throws IOException {
    StringBuilder sb = new StringBuilder();
    while (true) {
      readToken();
      if (lastToken == null) break;
      sb.append(lastToken.rep);
      if (lastToken.type == TemplateToken.Type.RC 
        && curlyStop == curlyCnt) break;
      if (lastToken.type == TemplateToken.Type.RB 
        && bracketStop == bracketCnt) break;
    } 
    if (w) Err.help("I'm skipping: " + sb);
  }
  
  private void readToken() throws IOException {
    lastToken = lexer.next();
    if (lastToken == null) return;
    log.finer("read token <" + lastToken.rep + "> of type " + lastToken.type);
    if (lastToken.type == TemplateToken.Type.LB) ++bracketCnt;
    if (lastToken.type == TemplateToken.Type.RB) --bracketCnt;
    if (lastToken.type == TemplateToken.Type.LC) ++curlyCnt;
    if (lastToken.type == TemplateToken.Type.RC) --curlyCnt;
    if (balancedWarning && (curlyCnt < 0 || bracketCnt < 0)) {
      err("You are on thin ice.");
      Err.help("I don't guarantee what happens if you use unbalaced [] or {}.");
      balancedWarning = false;
    }
  }
  
  private void switchOutput(Writer newOutput) throws IOException {
    if (output != null) output.flush();
    output = newOutput;
    if (output == null) 
      log.fine("Output is turned off.");
  }

  /*
   * Writes |id| using the case convention |cs|.
   */
  // candidate for memoization
  private void writeId(String id, TemplateToken.Case cs) throws IOException {
    StringBuilder res = new StringBuilder(id.length());
    boolean first = true;
    boolean prevIs_ = true;
    boolean prevIsUpper = false;
    for (int i = 0; i < id.length(); ++i) {
      char c = id.charAt(i);
      if (c == '_') prevIs_ = true;
      else {
        boolean thisIsUpper = Character.isUpperCase(c);
        if (prevIs_ || (thisIsUpper && !prevIsUpper)) {
          // beginning of word
          switch (cs) {
          case CAMEL_CASE:
            if (first) res.append(Character.toLowerCase(c));
            else res.append(Character.toUpperCase(c));
            break;
          case PASCAL_CASE:
            res.append(Character.toUpperCase(c));
            break;
          case LOWER_CASE:
            if (!first) res.append('_');
            res.append(Character.toLowerCase(c));
            break;
          case UPPER_CASE:
            if (!first) res.append('_');
            res.append(Character.toUpperCase(c));
          default:
            assert false;
          }
        } else {
          // the rest of letters
          switch (cs) {
          case UPPER_CASE:
            res.append(Character.toUpperCase(c));
            break;
          default:
            res.append(Character.toLowerCase(c));
          }
        }
        first = false;
        prevIs_ = false;
        prevIsUpper = thisIsUpper;
      }
    }
    write(res.toString());
  }
  
  /*
   * Sends |s| to the |output|.
   */
  private void write(String s) throws IOException {
    if (output != null) {
      output.write(s);
    }
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
