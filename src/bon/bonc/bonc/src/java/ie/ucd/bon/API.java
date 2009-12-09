/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.clinterface.BONcOptionsInterface;
import ie.ucd.bon.errorreporting.ExceptionalError;
import ie.ucd.bon.errorreporting.FileNotFoundError;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.display.PrefuseGraphDisplay;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.printer.BONPrintMonitor;
import ie.ucd.bon.source.SourceReader;
import ie.ucd.bon.util.StringUtil;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.Collection;

/**
 * The public API for BONc.
 * @author fintan
 */
public final class API {

  /**
   * Private constructor - cannot be instantiated.
   */
  private API() { }

  /**
   * Parse the provided input.
   * @param files the files to parse.
   * @param readFromStdIn a boolean indicating whether to also read input from stdin.
   * @param printTiming a boolean indicating whether timing information should be printed to stdout.
   * @return the ParsingTracker storing the results of the parse.
   */
  public static ParsingTracker parse(final Collection<File> files, final boolean readFromStdIn, final boolean printTiming) {
    ParsingTracker tracker = new ParsingTracker();

    if (readFromStdIn) {
      ParseResult parseResult = parseInput(SourceReader.getInstance().readStandardInput(), null, tracker, printTiming);
      if (parseResult != null) {
        tracker.addParse(null, parseResult);
      }
    }

    for (File file : files) {
      try {
        InputStream is = SourceReader.getInstance().readFile(file);

        ParseResult parseResult = parseInput(is, file, tracker, printTiming);
        if (parseResult != null) {
          tracker.addParse(file, parseResult);
        }
      } catch (FileNotFoundException fnfe) {
        tracker.addProblem(new FileNotFoundError(file));
      } catch (IOException ioe) {
        tracker.addProblem(new ExceptionalError(ioe));
        if (Main.isDebug()) {
          ioe.printStackTrace();
        }
      }
    }

    return tracker;
  }

  public static ParseResult parse(final InputStream is) {
    return Parser.parse(null, is);
  }
  
  public static ParseResult parse(String bonText) {
    return Parser.parse(null, new ByteArrayInputStream(bonText.getBytes()));
  }

  /**
   * Read from the given InputStream and parse what is read.
   * @param is the InputStream to read from.
   * @param file the File object representing where the InputStream is reading from.
   * @param tracker the ParsingTracker to store the results of this parse in.
   * @param printTiming a boolean indicating whether timing information should be printed to stdout.
   * @return a ParseResult object representing the result of parsing this input.
   */
  private static ParseResult parseInput(final InputStream is, final File file, final ParsingTracker tracker, final boolean printTiming) {
    if (printTiming) {
      long startTime = System.nanoTime();
      ParseResult parseResult = Parser.parse(file, is);
      if (parseResult.isValidParse()) {
        Parser.buildSymbolTable(parseResult, tracker);
      } else {
        Main.logDebug("Not building symbol table due to parse errors.");
      }
      long endTime = System.nanoTime();
      System.out.println("Parsing took: " + StringUtil.timeString(endTime - startTime));
      return parseResult;
    } else {
      ParseResult parseResult = Parser.parse(file, is);
      if (parseResult.isValidParse()) {
        Parser.buildSymbolTable(parseResult, tracker);
      } else {
        Main.logDebug("Not building symbol table due to parse errors.");
      }
      return parseResult;
    }
  }


  public static void print(final BONcOptionsInterface.Print printType, final boolean genClassDic, final File outputFile, final ParsingTracker tracker, final boolean extraWork, final boolean timing, final BONPrintMonitor monitor) {

    if (genClassDic && printType != BONcOptionsInterface.Print.DIC) {
      String classDic = Printer.printGeneratedClassDictionaryToString(tracker);
      File classDicAutoFile = new File("class-dic-auto");
      if (!classDic.equals("")) {
        tracker.addParse(classDicAutoFile, Parser.parse(classDicAutoFile, new ByteArrayInputStream(classDic.getBytes())));
      }
    }

    Printer.print(printType, outputFile, tracker, extraWork, timing, monitor);
  }
  
  public static void print(final BONcOptionsInterface.Print printType, final boolean genClassDic, final File outputFile, final ParsingTracker tracker, final boolean extraWork, final boolean timing) {
    print(printType, genClassDic, outputFile, tracker, extraWork, timing, BONPrintMonitor.JUST_PRINTS_MONITOR);
  }
      

  public static void printResults(final Problems problems, final ParsingTracker tracker, final PrintStream out) {
    printResults(problems, out);
    if (tracker != null) {
      tracker.printFinalMessage(out);
    }
  }

  public static void printResults(final Problems problems, final PrintStream out) {
    problems.printProblems(out);
    problems.printSummary(out);
  }

  public static void displayGraphs(final ParsingTracker tracker, final BONcOptionsInterface so) {
    if (so.isGraphSet()) {
      System.out.println("Graphing...");
      PrefuseGraphDisplay.displayGraph(so.getGraph(), tracker);
    }
  }

  public static Problems typeCheck(final ParsingTracker tracker, final boolean checkInformal, final boolean checkFormal, final boolean checkConsistency, final boolean typeCheck, final boolean timing) {
    Main.logDebug("typeCheck: " + typeCheck + ", checkInformal: " + checkInformal + ", checkFormal: " + checkFormal + ", checkConsistency: " + checkConsistency);

    if (timing) {
      long startTime = System.nanoTime();
      Problems problems = TypeChecker.typeCheck(tracker, typeCheck, checkInformal, checkFormal, checkConsistency);
      long endTime = System.nanoTime();
      System.out.println("Typechecking took: " + StringUtil.timeString(endTime - startTime));
      return problems;
    } else {
      return TypeChecker.typeCheck(tracker, typeCheck, checkInformal, checkFormal, checkConsistency);
    }
  }

  static Problems typeCheck(final ParsingTracker tracker, final BONcOptionsInterface so, final boolean timing) {
    return typeCheck(tracker, so.getCheckInformal(), so.getCheckFormal(), so.getCheckConsistency(), so.getTypecheck(), timing);
  }


  //TODO combined operations for a nicer interface in some situations. For example parseAndTypeCheck(final Collection<File> files, final boolean readFromStdIn, final boolean printTiming
}
