
package Ambit;

import Parser.Synex.Grammar.*;
import Parser.Synex.Parser.*;
import java.awt.TextArea;
import java.io.DataInputStream;
import java.io.StringBufferInputStream;
import java.util.Vector;
import java.util.Enumeration;

public class Console {

  private TextArea txtInput;
  private TextArea txtOutput;
  private Parser parser;
  private NonTerminal rootGrammar;
  private Ambient rootAmbient;
  private Ambient currentAmbient;
  private Vector topLevel;
  
  public Console() {
    this.txtInput = null;
    this.txtOutput = null;
    this.parser = null;
    this.rootGrammar = null;
    this.rootAmbient = null;
    this.currentAmbient = null;
    this.topLevel = null;
  }
  
  public void setupIO(TextArea txtInput, TextArea txtOutput) {
    this.txtInput = txtInput;
    this.txtOutput = txtOutput;
  }
  
  public void setupParser(Parser parser, NonTerminal rootGrammar) {
    this.parser = parser;
    this.rootGrammar = rootGrammar;
  }
  
  public void setupState() {
    resetState();
  }
  
  public synchronized void resetState() {
	txtOutput.setText("");
    rootAmbient = new Ambient(new Name("root"), new EnvEmpty(), this);
    currentAmbient = rootAmbient;
    topLevel = new Vector();
    topLevel.addElement(rootAmbient);
  }

  public synchronized void showState(String msg) {
    // synchronized so that console is held until state is computed and printed.
	txtOutput.appendText(msg + "State: " + getState() + "\n");
  }

  public synchronized String getState() {
	return rootAmbient.toString();
  }

  public synchronized void setOutput(String string) {
	txtOutput.setText(string);
  }

  public synchronized void appendOutput(String string) {
	txtOutput.appendText(string);
  }

  public synchronized void markedAmbient(Ambient ambient) {
    //-- check for duplicates
    topLevel.addElement(ambient);
    appendOutput("Marked: " + ambient.getName().toString() + "\n");
  }
  
  public synchronized void execAgent() {
     try {       
        // new input to the  parser
        String newInput = txtInput.getText();
        DataInputStream inputStream = new DataInputStream(new StringBufferInputStream(newInput));
        parser.reset();
        parser.readFrom("AppletInput", inputStream);
        
        // parse
	    setOutput("");
        Outcome outcome = parser.parse(rootGrammar);
        
        // process result of parsing
        if (outcome instanceof ParseFailure) {
          ParseFailure failure = (ParseFailure)outcome;
	      txtInput.select(0, failure.endLocation.chr);
          appendOutput("Parsing failure: \n" + parser.syntaxErrorMsg(failure));
        } else {
          txtInput.selectAll();
          // parser debugging
          appendOutput("Parsed: " + outcome.toString() + "\n");
        }

        // execute
        if (outcome instanceof CodeProc) {
          CodeProc proc = (CodeProc)outcome;
          currentAmbient.startAgent(proc, currentAmbient.getInitEnv());
	    } else if (outcome instanceof CodeTopFocus) {
          CodeTopFocus focus = (CodeTopFocus)outcome;
          Ambient focusAmbient = null;
          Enumeration enumAmbients = topLevel.elements();
          while (enumAmbients.hasMoreElements()) {
            Ambient nextAmbient = (Ambient)enumAmbients.nextElement();
            if (nextAmbient.getName().matches(focus.ide)) {
              focusAmbient = nextAmbient;
              break;
            }
          }
          if (focusAmbient == null) {
            appendOutput("Ambient not found: " + focus.ide + "\n");
          } else {
            currentAmbient = focusAmbient;
            appendOutput("Focus: @" + focusAmbient.toString() + "\n");
            appendOutput("Env: " + currentAmbient.getInitEnv().toString() + "\n");
          }
        }

        // declare
//      if (outcome instanceof CodeLet, which is not Code) {
//        txtInput.setText("");
//	      txtOld.appendText(newInput + "\n");
//	      topLevelEnv = ((CodeLet)outcome).addBinding(topLevelEnv);
//        appendOutput("Binding added to top-level environment.");
//      } catch (ExecException e) {
//	        appendOutput("Error while evaluating: " + e.getMessage());
//	    }

	  } catch (java.lang.Exception ex) {
	    appendOutput("Java Exception: " + ex.getMessage());
//      ex.printStackTrace();
//	    System.exit(-1);
//	  } finally {
//	    java.lang.System.gc();
	  }
  }

}

/*
	    } else if (outcome instanceof CodeTopCreate) {
          CodeTopCreate create = (CodeTopCreate)outcome;
          Name newName = new Name(create.ide);
          Env newEnv = new EnvCons(create.ide, newName, currentAmbient.getInitEnv());      
          Ambient newAmbient = currentAmbient.newOwnAmbient(newName, newEnv);
	      topLevel.addElement(newAmbient);
          appendOutput("Created: " + create.ide + "\n");
*/
