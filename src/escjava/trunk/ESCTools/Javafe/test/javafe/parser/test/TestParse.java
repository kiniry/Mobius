/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.parser.test;


import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.FileInputStream;
import java.io.PrintStream;

import javafe.ast.CompilationUnit;
import javafe.ast.PrettyPrint;
import javafe.parser.Lex;
import javafe.parser.Parse;
import javafe.util.CorrelatedReader;
import javafe.util.FileCorrelatedReader;
import javafe.util.Assert;
import javafe.util.ErrorSet;


public class TestParse {
  // The parser and scanner used to process files
  //@ invariant lexer!=null
  public static Lex lexer = new Lex(null, true);

  //@ invariant parser!=null
  public static Parse parser = new Parse();

  // The following variables are set by command-line options
  public static boolean check = false;
  public static boolean print = false;
  public static boolean progress = false;
  public static boolean verboseprogress = false;
  public static boolean idempotence = false;

  // Buffers used to hold intermediate results
  //@ invariant out1!=null && out2!=null
  public static MemoryPipeOutputStream out1 = new MemoryPipeOutputStream();
  public static MemoryPipeOutputStream out2 = new MemoryPipeOutputStream();

    //@ ensures false
    public static void fatal(String msg) {
	System.err.println("Fatal error: " + msg);
	System.exit(99);
    }


  //@ requires \nonnullelements(argv)
  public static void main(String[] argv) throws IOException {

     // Allow for a test of the diff routine:
    if (argv.length>0 && argv[0].equals("diff")) {
      if (argv.length<3)
	fatal("Insufficient arguments to diff");
      diff(argv[1], new FileInputStream(argv[1]),new FileInputStream(argv[2]));
      System.exit(0);
    }

    int exitStatus = 0;
    for(int i = 0; i<argv.length; i++) {
      if (argv[i].equals("verboseprogress")) { verboseprogress=true;continue; }
      else if (argv[i].equals("check")) { check = true; continue; }
      else if (argv[i].equals("print")) { print = true; continue; }
      else if (argv[i].equals("progress")) { progress = true; continue; }
      else if (argv[i].equals("silent")) { ErrorSet.gag = true; continue; }
      else if (argv[i].equals("idempotence")) { idempotence = true; continue; }

      if (verboseprogress) System.out.println("Checking: " + argv[i]);
      else if (progress) {
	System.out.write('.');
	if (i != 0 && (i % 50) == 0) System.out.write('\n');
	System.out.flush();
      }

      out1.reset();
      out2.reset();
      prettyPrint(argv[i], 
		  new FileInputStream(argv[i]), out1, 
		  check, print);
      if (idempotence) {
	prettyPrint(argv[i] + ":printed", out1.getInputStream(), out2, 
		    false, false);
	if (diff(argv[i], out1.getInputStream(), out2.getInputStream()))
	  exitStatus = 2;
      }
    }
    if (progress) System.out.println("");
    System.exit(exitStatus);
  }

  //@ requires n!=null
  //@ requires src!=null && dst!=null
  public static void prettyPrint(String n, InputStream src, OutputStream dst,
				 boolean check, boolean print) {
    CorrelatedReader in = new FileCorrelatedReader(src, n);
    PrintStream out = new PrintStream(dst);
    lexer.restart(in);
    CompilationUnit cu = parser.parseCompilationUnit(lexer, false);
    if (check) cu.check();
    PrettyPrint.inst.print(out, cu);
    if (print) PrettyPrint.inst.print(System.out, cu);
    in.close();
    out.close();
  }

  /** Compares two files.  Prints a message and returns true if they're
    different; otherwise, returns false. */

  //@ requires in1!=null && in2!=null
  public static boolean diff(String n, InputStream in1, InputStream in2) {
    try {
      int c1 = in1.read(), c2 = in2.read();
      int line = 1, col = 1, offset = 1;
      while (c1 == c2 && c1 != -1 && c2 != -1) {
	if (c1 == '\n') { line++; col = 1; }
	else col++;
	offset++;
	c1 = in1.read();
	c2 = in2.read();
      }
      if (c1 != c2) {
	if (progress) n = "\n" + n;
	System.out.println(n + " failed (" + c1 + " != " + c2
			   + " at offset " + offset
			   + ", line " + line + ", col " + col + ")");
	return true;
      } else return false;
    } catch(IOException e) {
      e.printStackTrace();
      System.exit(2);
      return false; // Dummy
    }
  }
}

final class MemoryPipeOutputStream extends OutputStream {
  //@ invariant buff!=null
  byte[] buff = new byte[16*1024];

  int outi = 0;

  //@ invariant ini>=0  
  //@ invariant ini<=buff.length
  int ini = 0;

  public void write(int b) {
    try {
      buff[ini] = (byte)b;	//@ nowarn IndexTooBig  // caught
      ini++;
    } catch (ArrayIndexOutOfBoundsException e) {
      byte[] newbuff = new byte[2*buff.length];
      System.arraycopy(buff, 0, newbuff, 0, buff.length);
      buff = newbuff;
      buff[ini++] = (byte)b;
    }
  }

  void reset() { ini = 0; }

  //@ ensures \result!=null
  MemoryPipeInputStream getInputStream()
    { return new MemoryPipeInputStream(this); }
}

final class MemoryPipeInputStream extends InputStream {
  //@ invariant src!=null
  MemoryPipeOutputStream src;

  //@ invariant outi>=0
  int outi = 0;

  //@ requires src!=null
  MemoryPipeInputStream(MemoryPipeOutputStream src) { this.src = src; }

  public int read() {
    int result = src.ini <= outi ? -1
				 : src.buff[outi++];
    return result;
  }
}
