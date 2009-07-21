/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import java.io.File;
import java.io.IOException;
import org.xml.sax.Attributes;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * This class parses project's .classpath file to extract the build path.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ClassPathParser extends DefaultHandler {

  /**
   * Build path of the project.
   */
  private String my_build_path;

  /**
   * This method parses project's .classpath file to extract the build path.
   * After that the {@link ClassPathParser#getBuildPath()} method returns
   * the build path.
   *
   * @param a_path a path to .classpath file
   */
  public void parseDocument(final String a_path) {
    final SAXParserFactory spf = SAXParserFactory.newInstance();
    try {
      final SAXParser sp = spf.newSAXParser();
      sp.parse(new File(a_path), this);
    } catch (SAXException se) {
      se.printStackTrace();
    } catch (ParserConfigurationException pce) {
      pce.printStackTrace();
    } catch (IOException ie) {
      ie.printStackTrace();
    }
  }

  /**
   * Standard SAX method for processing XML element.
   * Receive notification of the beginning of an element.
   *
   * @param an_uri - the Namespace URI, or the empty string if the element
   * has no Namespace URI or if Namespace processing is not being performed
   * @param a_local_name - the local name (without prefix), or the empty
   * string if Namespace processing is not being performed
   * @param a_q_name - the qualified name (with prefix), or the empty string
   * if qualified names are not available
   * @param an_attributes - the attributes attached to the element. If there
   * are no attributes, it shall be an empty Attributes object. The value
   * of this object after startElement returns is undefined
   * @throws SAXException - any SAX exception, possibly wrapping another
   * exception
   */
  public void startElement(final String an_uri, final String a_local_name,
                           final String a_q_name,
                           final Attributes an_attributes) throws SAXException {
    super.startElement(an_uri, a_local_name, a_q_name, an_attributes);
    if (a_q_name.equalsIgnoreCase("classpathentry")) {
      if (an_attributes.getValue("kind").equalsIgnoreCase("output")) {
        my_build_path = an_attributes.getValue("path");
      }
    }
  }

  /**
   * Standard SAX method for processing XML element.
   * Receive notification of the end of an element.
   *
   * @param an_uri - the Namespace URI, or the empty string if the element
   * has no Namespace URI or if Namespace processing is not being performed
   * @param a_local_name - the local name (without prefix), or the empty
   * string if Namespace processing is not being performed
   * @param a_q_name - the qualified name (with prefix), or the empty string
   * if qualified names are not available
   * @throws SAXException - any SAX exception, possibly wrapping another
   * exception
   */
  public void endElement(final String an_uri,  final String a_local_name,
                         final String a_q_name) throws SAXException {

  }

  /**
   * Returns build path of the project.
   * @return build path of the project
   */
  public String getBuildPath() {
    return my_build_path;
  }

}
