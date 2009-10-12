/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.util;

import java.io.IOException;
import java.io.Writer;
import java.util.Stack;

/**
 * Adapted from Henri Yandell's version at http://www.generationjava.com/projects/XmlWriter.shtml
 */
public class XMLWriter {

  private static String NEW_LINE = System.getProperty("line.separator");

  private Writer writer; // underlying writer
  private Stack<String> stack; // of xml entity names
  private StringBuffer attrs; // current attribute string
  private boolean empty;      // is the current node empty
  private boolean closed;     // is the current node closed...

  private int indentation;

  private static final int NUM_SPACES_PER_INDENT = 2;

  /**
   * Create an XmlWriter on top of an existing java.io.Writer.
   */
  public XMLWriter(Writer writer) {
    this.writer = writer;
    this.closed = true;
    this.stack = new Stack<String>();
    this.indentation = 0;
  }

  /**
   * Begin to output an entity.
   *
   * @param name name of entity.
   */
  public XMLWriter writeEntity(String name) throws IOException {
    closeOpeningTag();
    this.closed = false;

    this.writer.write(NEW_LINE);
    for (int i = 0; i < NUM_SPACES_PER_INDENT * indentation; i++) {
      this.writer.write(' ');
    }

    this.writer.write("<");
    this.writer.write(name);
    stack.add(name);
    this.empty = true;
    indentation++;

    return this;
  }

  // close off the opening tag
  private void closeOpeningTag() throws IOException {
    if (!this.closed) {
      writeAttributes();
      this.closed = true;
      this.writer.write(">");
    }
  }

  // write out all current attributes
  private void writeAttributes() throws IOException {
    if (this.attrs != null) {
      this.writer.write(this.attrs.toString());
      this.attrs.setLength(0);
      this.empty = false;
    }
  }

  /**
   * Write an attribute out for the current entity.
   * Any xml characters in the value are escaped.
   * Currently it does not actually throw the exception, but
   * the api is set that way for future changes.
   *
   * @param String name of attribute.
   * @param String value of attribute.
   */
  public XMLWriter writeAttribute(String attr, String value) throws IOException {

    if (this.attrs == null) {
      this.attrs = new StringBuffer();
    }
    this.attrs.append(" ");
    this.attrs.append(attr);
    this.attrs.append("=\"");
    this.attrs.append(escapeXml(value));
    this.attrs.append("\"");
    return this;
  }

  /**
   * End the current entity. This will throw an exception
   * if it is called when there is not a currently open
   * entity.
   */
  public XMLWriter endEntity() throws IOException {
    indentation--;
    if (this.stack.empty()) {
      throw new IOException("Called endEntity too many times. ");
    }
    String name = this.stack.pop();
    if (name != null) {
      if (this.empty) {
        writeAttributes();
        this.writer.write("/>");
      } else {
        this.writer.write(NEW_LINE);
        for (int i = 0; i < NUM_SPACES_PER_INDENT * indentation; i++) {
          this.writer.write(' ');
        }
        this.writer.write("</");
        this.writer.write(name);
        this.writer.write(">");
      }
      this.empty = false;
      this.closed = true;
    }

    return this;
  }

  /**
   * Close this writer. It does not close the underlying
   * writer, but does throw an exception if there are
   * as yet unclosed tags.
   */
  public void close() throws IOException {
    if (!this.stack.empty()) {
      throw new IOException("Tags are not all closed. " + "Possibly, "+this.stack.pop()+" is unclosed. ");
    }
  }

  /**
   * Output body text. Any xml characters are escaped.
   */
  public XMLWriter writeText(String text) throws IOException {
    closeOpeningTag();
    this.empty = false;
    this.writer.write(escapeXml(text));
    return this;
  }

  // from XmlW
  public static String escapeXml(String str) {
    str = replaceString(str,"&","&amp;");
    str = replaceString(str,"<","&lt;");
    str = replaceString(str,">","&gt;");
    str = replaceString(str,"\"","&quot;");
    str = replaceString(str,"'","&apos;");
    return str;
  }

  // from StringW
  public static String replaceString(String text, String repl, String with) {
    return replaceString(text, repl, with, -1);
  }
  /**
   * Replace a string with another string inside a larger string, for
   * the first n values of the search string.
   *
   * @param text String to do search and replace in
   * @param repl String to search for
   * @param with String to replace with
   * @param n    int    values to replace
   *
   * @return String with n values replacEd
   */
  static public String replaceString(String text, String repl, String with, int max) {
    if (text == null) {
      return null;
    }

    StringBuffer buffer = new StringBuffer(text.length());
    int start = 0;
    int end = 0;
    while ((end = text.indexOf(repl, start)) != -1) {
      buffer.append(text.substring(start, end)).append(with);
      start = end + repl.length();

      if (--max == 0) {
        break;
      }
    }
    buffer.append(text.substring(start));

    return buffer.toString();
  }


}
