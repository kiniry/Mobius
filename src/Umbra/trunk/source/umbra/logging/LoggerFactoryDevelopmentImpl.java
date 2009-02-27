/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.logging;

import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.Handler;
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.SimpleFormatter;

/**
 * @version a-01
 *
 */
public class LoggerFactoryDevelopmentImpl extends LoggerFactoryImpl {

  /* (non-Javadoc)
   * @see umbra.logging.LoggerFactoryImpl#getClassLogger(java.lang.Class)
   */
  @Override
  public Logger getClassLogger(final Class<?> c) {
    String className = c.getName();
    
    Logger logger = Logger.getLogger(c.getName());
    logger.setLevel(Level.ALL);
    
    for (Handler h : logger.getHandlers()) {
      h.setLevel(Level.INFO);
    }
    
  /*  try {
      FileHandler fileHandler = new FileHandler(logPath + className + logSuffix);
      fileHandler.setLevel(Level.ALL);
      Formatter formatter = new SimpleFormatter();
      fileHandler.setFormatter(formatter);
      
      logger.addHandler(fileHandler);
    } catch (SecurityException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } */
    
    return logger;
  }

}
