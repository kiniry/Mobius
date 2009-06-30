package genericutils;

import java.io.*;
import java.util.EnumSet;
import java.util.HashMap;

import com.google.common.collect.Maps;
import com.google.common.base.Supplier;

/**
  A lightweight logger with a configurable sink that knows
  about categories and levels. Categories are taken from some
  {@code Enum} set by the user; levels are taken from some
  {@code Enum} set by the user.

  @param <L> the type of the levels
  @param <C> the type of the categories
 */
public class Logger<L extends Enum<L>, C extends Enum<C>> {
  private static HashMap<String, Logger> instances = Maps.newHashMap();
  private PrintWriter sink;
  private L thresholdLevel;
  private EnumSet<C> enabledCategories;

  private Logger() {
    sink = new PrintWriter(System.out, true);
  }

  public static <L,C> Logger get(String name) {
    Logger r = instances.get(name);
    if (r == null) {
      r = new Logger();
      instances.put(name, r);
    }
    return r;
  }

  // The main sink setter, plus convenience ones.
  public void sink(PrintWriter sink) throws IOException {
    this.sink = sink; 
  }

  public void sink(OutputStream sink) throws IOException { 
    sink(new PrintWriter(sink, true)); 
  }

  public void sink(Writer sink) throws IOException { 
    sink(new PrintWriter(sink, true)); 
  }

  public void sink(String sink) throws IOException { 
    sink(new PrintWriter(sink)); 
  }

  public void sink(File sink) throws IOException { 
    sink(new PrintWriter(sink)); 
  }

  // === Methods for setting up the behavior of this class ===
  public void level(L thresholdLevel) {
    this.thresholdLevel = thresholdLevel;
  }
  
  public void enable(C category) {
    if (enabledCategories == null)
      enabledCategories = EnumSet.of(category);
    else
      enabledCategories.add(category);
  }

  public void disable(C category) {
    if (enabledCategories == null) return;
    enabledCategories.remove(category); 
  }

  // === Main methods for using this class ===

  /** To be used when computing the log message is time consuming. */
  public void log(C c, L l, Supplier<String> s) {
    if (isWritable(c, l)) internalLog(s.get());
  }

  public void log(C c, L l, String m) {
    if (isWritable(c, l)) internalLog(m);
  }


  // === Helpers ===
  private void internalLog(String m) {
    sink.println(m);
  }

  private boolean isWritable(C c, L l) {
    return 
      enabledCategories != null &&
      thresholdLevel != null &&
      enabledCategories.contains(c) &&
      l.compareTo(thresholdLevel) >= 0;
  }
}
