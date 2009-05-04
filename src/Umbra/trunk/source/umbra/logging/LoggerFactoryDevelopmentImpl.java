/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.logging;

import java.io.File;
import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.Handler;
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.SimpleFormatter;

/**
 * @author szymon wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 */
public class LoggerFactoryDevelopmentImpl extends LoggerFactoryImpl {

  /**
   *
   */
  LoggerFactoryDevelopmentImpl() {
    super("umbra_logs/dvpmt/");
  }

  /**
   * @param a_class a class
   * @return new class logger
   */
  @Override
  public Logger getClassLogger(final Class < ? > a_class) {
    final String className = a_class.getName();
    final Logger logger = Logger.getLogger(className);
    logger.setLevel(Level.ALL);

    for (Handler h : logger.getHandlers()) {
      h.setLevel(Level.WARNING);
    }

    try {
      final FileHandler fileHandler = new FileHandler(
              getLogPath() + className + getLogSuffix());
      fileHandler.setLevel(Level.ALL);
      final Formatter formatter = new SimpleFormatter();
      fileHandler.setFormatter(formatter);

      logger.addHandler(fileHandler);
    } catch (SecurityException e) {
      e.printStackTrace();
    } catch (IOException e) {
      System.out.println("mkdir: " +
         System.getProperty("user.dir") + "/" + getLogPath());
      final boolean ok = (new File(getLogPath())).mkdirs();
      if (ok) {
        System.out.println("done");
      } else {
        System.out.println("fail");
      }
    }
    return logger;
  }

}
