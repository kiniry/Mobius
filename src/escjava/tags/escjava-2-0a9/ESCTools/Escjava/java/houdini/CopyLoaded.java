/* Copyright 2000, 2001, Compaq Computer Corporation */


package houdini;

import javafe.Tool;

import java.util.Vector;

import javafe.ast.*;
import javafe.tc.*;
import javafe.util.*;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.*;

import java.util.StringTokenizer;

import escjava.ast.*;
import escjava.reader.*;
import escjava.parser.*;

import javafe.parser.*;
import javafe.reader.*;

public class CopyLoaded extends javafe.CopyLoaded implements Listener {

    public CopyLoaded() {
	super();
	escjava.Main.nvu = true; // fix pretty printed names in quantified formulas
    }

    //@ requires \nonnullelements(args);
    public static void main(String[] args) {
	Tool t = new CopyLoaded();
	t.run(args);
    }

    /**
     ** Returns the Esc StandardTypeReader, EscTypeReader.
     **/
    public StandardTypeReader makeStandardTypeReader(String path,
						     PragmaParser P) {
        return EscTypeReader.make(path, P);
    }

    /**
     ** Returns the EscPragmaParser.
     **/
    public javafe.parser.PragmaParser makePragmaParser() {
      return new escjava.parser.EscPragmaParser();
    }

    /**
     ** Returns the pretty printer to set
     ** <code>PrettyPrint.inst</code> to.
     **/
    public PrettyPrint makePrettyPrint() {
      DelegatingPrettyPrint p = new EscPrettyPrint();
      p.del = new StandardPrettyPrint(p);
      return p;
    }

    /**
     ** Called to obtain an instance of the javafe.tc.TypeCheck class
     ** (or a subclass thereof). May not return <code>null</code>.  By
     ** default, returns <code>javafe.tc.TypeCheck</code>.
     **/
    public javafe.tc.TypeCheck makeTypeCheck() {
	return new escjava.tc.TypeCheck();
    }
    

}
