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
public class Logger<C extends Enum<C>, L extends Enum<L>> {
  private static HashMap<String, Logger> instances = Maps.newHashMap();
  private PrintWriter sink;
  private L thresholdLevel;
  private EnumSet<C> enabledCategories;
  private boolean verbose;

  private Logger() {
    verbose = false;
  }

  public static <C extends Enum<C>, L extends Enum<L>>
  Logger<C, L> get(String name) {
    @SuppressWarnings("unchecked") // TODO: put some checks
    Logger<C, L> r = instances.get(name);
    if (r == null) {
      r = new Logger<C, L>();
      instances.put(name, r);
    }
    return r;
  }

  // The main sink setter, plus convenience ones.
  public void sink(PrintWriter sink) {
    this.sink = sink; 
  }

  public void sink(OutputStream sink) { 
    sink(new PrintWriter(sink, true)); 
  }

  public void sink(Writer sink) { 
    sink(new PrintWriter(sink, true)); 
  }

  public void sink(String sink) throws IOException { 
    sink(new PrintWriter(sink)); 
  }

  public void sink(File sink) throws IOException { 
    sink(new PrintWriter(sink)); 
  }

  // === Methods for setting up the behavior of this class ===
  public void verbose(boolean verbose) {
    this.verbose = verbose;
  }

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
  public void say(C c, L l, Supplier<String> s) {
    if (isWritable(c, l)) internalLog(c, l, s.get());
  }

  public void say(C c, L l, String m) {
    if (isWritable(c, l)) internalLog(c, l, m);
  }

  public void say(String m) {
    if (sink != null) sink.println(m);
  }

  // === Helpers ===
  private void internalLog(C c, L l, String m) {
    if (verbose) 
      m = "" + c + " " + l + " " + System.currentTimeMillis() + " " + m;
    say(m);
  }

  private boolean isWritable(C c, L l) {
    return 
      enabledCategories != null &&
      thresholdLevel != null &&
      enabledCategories.contains(c) &&
      l.compareTo(thresholdLevel) >= 0;
  }
}
