
package Ambit;

import java.io.IOException;

import Ambit.Console;

import Parser.Synex.SynexException;
import Parser.Synex.Grammar.*;
import Parser.Synex.Parser.*;
import Parser.Synex.Scanner.*;
import Parser.SynexClient.ScannerOne;
import Parser.SynexClient.TokenClient.*;

public class Productions {

  public void setup(Console console) {
    try {       
      // setup parser
      ScannerOne scanner = new ScannerOne();
      Parser parser = new Parser(scanner);
      // setup grammar
      NonTerminal rootGrammar = setupProductions(scanner);
      console.setupParser(parser, rootGrammar);
      // setup state
      console.setupState();
    } catch (SynexException ex) {
	  console.setOutput("Exception at setup: " + ex.getMessage());
    }
  }
  
  NonTerminal setupProductions(ScannerOne scanner) throws BadGrammarException {
//     root ::= statement EOF
//     
//     statement ::= { process }  
//        
//     let ::= 
//       [ "let" IDE "(" ideList ")" "=" simpleProcess ";" process ]
//     
//     topFocus ::= [ "at" IDE ]
//     
//     simpleTerm ::=
//       { IDE
//         STRING
//         REAL
//         [ "in" IDE ]                                entry capability                                 
//         [ "out" IDE ]                               exit capability
//         [ "open" IDE ]                              open capability
//         [ "stay" ]                                  empty route
//         [ "(" term ")" ]
//
//     term ::=
//       [ simpleTerm 
//         { [ "&" term ] [] }                          routes (capability lists)
//       ]
//
//     process ::=
//       [ simpleProcess { [ '|' process ] [] } ]
//
//     ideEtc ::=
//       [ x:=IDE { ambient(x) letExpansion(x) procIde(x) } ]
//
//     ambient(x) ::=
//       [ "[" { process | [] } "]" ]                    ambient
//
//     letExpansion(x) ::=
//       [ "(" termList ")" { [ "@" term ] [] }]         let expansion
//
//     procIde(x) ::=
//       []                                              procIde
//         
//     markedAmbient ::=
//       [ "@" IDE "[" { process | [] } "]" ]            ambient
//         
//     simpleProcess ::=
//       { ideEtc
//         markedAmbient
//         -                                              stop
//         #                                              implode
//         [ "new" newProcess ]                           new name(s)
//         [ "rec" IDE "." simpleProcess ]                recursion
//         [ "do" term optDotSimpleProcess ]              action
//         [ STR optDotSimpleProcess ]                    screams
//         [ "(" process ")" ]                            parentheses
//         [ "ask" IDE optDotSimpleProcess ]
//         [ "say" term optDotSimpleProcess ]
//         [ "be" term optDotSimpleProcess ]
//         [ "wait" term optDotSimpleProcess ]
//         let
//       }
//
//     optDotSimpleProcess ::=
//       { [ "." simpleProcess ] | [] }
//
//     newProcess ::=
//       [ IDE { [ "." process ] newProcess } ]

    NonTerminal root = new NonTerminal();
    NonTerminal statement = new NonTerminal();     
    NonTerminal let = new NonTerminal();
    NonTerminal ideList = new NonTerminal();
    NonTerminal termList = new NonTerminal();
    NonTerminal topFocus = new NonTerminal();
    NonTerminal simpleTerm = new NonTerminal();
    NonTerminal term = new NonTerminal();
    NonTerminal ide = new NonTerminal();
    NonTerminal string = new NonTerminal();
    NonTerminal real = new NonTerminal();
    NonTerminal inCap = new NonTerminal();
    NonTerminal outCap = new NonTerminal();
    NonTerminal openCap = new NonTerminal();
    NonTerminal stay = new NonTerminal();
    NonTerminal process = new NonTerminal();
    NonTerminal newProcess = new NonTerminal();
    NonTerminal nullProcess = new NonTerminal();
    NonTerminal ideEtc = new NonTerminal();
    NonTerminal ambient = new NonTerminal();
    NonTerminal letExpansion = new NonTerminal();
    NonTerminal procIde = new NonTerminal();
    NonTerminal markedAmbient = new NonTerminal();
    NonTerminal simpleProcess = new NonTerminal();
    NonTerminal optDotSimpleProcess = new NonTerminal();
    NonTerminal stop = new NonTerminal();
    NonTerminal implode = new NonTerminal();
    NonTerminal enact = new NonTerminal();
    NonTerminal newName = new NonTerminal();
    NonTerminal recursion = new NonTerminal();
    NonTerminal scream = new NonTerminal();
    NonTerminal parProcess = new NonTerminal();
    NonTerminal parTerm = new NonTerminal();
    NonTerminal ask = new NonTerminal();
    NonTerminal say = new NonTerminal();
    NonTerminal be = new NonTerminal();
    NonTerminal wait = new NonTerminal();
    
/*
    NonTerminal con = new NonTerminal();
    NonTerminal conInt = new NonTerminal();
    NonTerminal conChar = new NonTerminal();
    NonTerminal conStr = new NonTerminal();
*/
  
    root.production("root", ActionFetch.fetch0, 1, 0,
      new Sequence(new GrammarList(
        new Store(0, statement),
        new Terminal(new TokenEOF())
      ))
    );

    statement.production("statement", ActionNeutral.neutral, 0, 0,
      new Choice(new GrammarList(
        topFocus, process
      ))
    );

    let.production("let", new ActionLet(), 4, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("let", scanner)),
        new Store(0, new TerminalFamily(new TokenIde(""))),
        new Terminal(new TokenDelim('(', scanner)),
        new Store(1, ideList),
        new Terminal(new TokenDelim(')', scanner)),
        new Terminal(new TokenDelim('=', scanner)),
        new Store(2, simpleProcess),
        new Terminal(new TokenDelim(';', scanner)),
        new GrammarList(
        new Store(3, process))
      ))
    );

    ideList.production("ideList", new ActionIdeList(), 2, 0,
      new Choice(new GrammarList(
        new Sequence(new GrammarList(
          new Store(0, new TerminalFamily(new TokenIde(""))),
          new Store(1, ideList)
        )),
        new Sequence(null)
      ))
    );

    termList.production("termList", new ActionTermList(), 2, 0,
      new Choice(new GrammarList(
        new Sequence(new GrammarList(
          new Store(0, term),
          new Store(1, termList)
        )),
        new Sequence(null)
      ))
    );
    
    topFocus.production("topFocus", new ActionTopFocus(), 1, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("at", scanner)),
        new Store(0, new TerminalFamily(new TokenIde("")))
      ))
    );

    term.production("term", new ActionRoute(), 2, 0,
      new Sequence(new GrammarList(
        new Store(0, simpleTerm),
        new Choice(new GrammarList(
          new Sequence(new GrammarList(
            new Terminal(new TokenDelim('&', scanner)),
            new Store(1, term)	
          )),
          new Sequence(null)
        ))
      ))
    );

    simpleTerm.production("simpleTerm", ActionNeutral.neutral, 0, 0,
      new Choice(new GrammarList(
        ide, string, real, inCap, outCap, openCap, stay, parTerm
      ))
    );

    ide.production("ide", new ActionIde(), 0, 0,
      new TerminalFamily(new TokenIde(""))
    );

    string.production("string", new ActionString(), 0, 0,
      new TerminalFamily(new TokenString(""))
    );

    real.production("real", new ActionReal(), 0, 0,
      new TerminalFamily(new TokenReal(0.0))
    );

    inCap.production("inCap", new ActionInCap(), 1, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("in", scanner)),
        new Store(0, ide)
      ))
    );

    outCap.production("outCap", new ActionOutCap(), 1, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("out", scanner)),
        new Store(0, ide)
      ))
    );

    openCap.production("openCap", new ActionOpenCap(), 1, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("open", scanner)),
        new Store(0, ide)
      ))
    );

    stay.production("stay", new ActionStay(), 0, 0,
      new Terminal(new TokenKey("stay", scanner))
    );

    parTerm.production("parTerm", ActionFetch.fetch0, 1, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenDelim('(', scanner)),
        new Store(0, term),
        new Terminal(new TokenDelim(')', scanner))
      ))
    );      

    process.production("process", new ActionParallel(), 2, 0,
      new Sequence(new GrammarList(
        new Store(0, simpleProcess),
        new Choice(new GrammarList(
          new Sequence(new GrammarList(
            new Terminal(new TokenDelim('|', scanner)),
            new Store(1, process)	
          )),
          new Sequence(null)
        ))
      ))
    );

    ideEtc.production("ideEtc", ActionFetch.fetch1, 2, 0,
      new Sequence(new GrammarList(
        new Store(0, new TerminalFamily(new TokenIde(""))),
        new Store(1,
          new Choice(new GrammarList(
            new Apply(ambient, new Args(0, null)),
            new Apply(letExpansion, new Args(0, null)),
            new Apply(procIde, new Args(0, null))
          ))
        )
      ))
    );

    ambient.production("ambient", new ActionAmbient(), 2, 1,
      new Sequence(new GrammarList(
        new Terminal(new TokenDelim('[', scanner)),
        new Choice(new GrammarList(
          new Store(1, process),
          new Store(1, nullProcess))),
        new Terminal(new TokenDelim(']', scanner))
      ))
    );

    letExpansion.production("letExpansion", new ActionLetExpansion(), 3, 1,
      new Sequence(new GrammarList(
        new Terminal(new TokenDelim('(', scanner)),
        new Store(1, termList),
        new Terminal(new TokenDelim(')', scanner)),
        new Choice(new GrammarList(
          new Sequence(new GrammarList(
            new Terminal(new TokenKey("at", scanner)),
            new Store(2, term))),
          new Sequence(null)
          ))
      ))
    );

    procIde.production("procIde", new ActionProcIde(), 1, 1,
      new Sequence(null)
    );

    markedAmbient.production("markedAmbient", new ActionMarkedAmbient(), 2, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("@", scanner)),
        new Store(0, new TerminalFamily(new TokenIde(""))),
        new Terminal(new TokenDelim('[', scanner)),
        new Choice(new GrammarList(
          new Store(1, process),
          new Store(1, nullProcess))),
        new Terminal(new TokenDelim(']', scanner))
      ))
    );

    nullProcess.production("nullProcess", new ActionStop(), 0, 0,
      new Sequence(null)
    );

    simpleProcess.production("simpleProcess", ActionNeutral.neutral, 0, 0,
      new Choice(new GrammarList(
         parProcess, ideEtc, markedAmbient, stop, implode, enact, newName, recursion,
           new GrammarList(scream, ask, say, be, wait, let
      )))
    );

    stop.production("stop", new ActionStop(), 0, 0,
      new Terminal(new TokenKey("-", scanner))
    );

    implode.production("implode", new ActionImplode(), 0, 0,
      new Terminal(new TokenKey("#", scanner))
    );

    enact.production("enact", new ActionEnact(), 2, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("do", scanner)),
        new Store(0, term),
        new Store(1, optDotSimpleProcess)
      ))
    );

    scream.production("scream", new ActionScream(), 2, 0,
      new Sequence(new GrammarList(
        new Store(0, new TerminalFamily(new TokenString(""))),
        new Store(1, optDotSimpleProcess)
      ))
    );

    newName.production("newName", ActionFetch.fetch0, 1, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("new", scanner)),
        new Store(0, newProcess)
      ))
    );
    
    newProcess.production("newProcess", new ActionNew(), 2, 0,
      new Sequence(new GrammarList(
        new Store(0, new TerminalFamily(new TokenIde(""))),
        new Choice(new GrammarList(
          new Sequence(new GrammarList(
            new Terminal(new TokenDelim('.', scanner)),	
            new Store(1, process)
          )),
          new Store(1, newProcess)
        ))
      ))
    );
    

    recursion.production("recursion", new ActionRecursion(), 2, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("rec", scanner)),
        new Store(0, new TerminalFamily(new TokenIde(""))),
        new Terminal(new TokenDelim('.', scanner)),	
        new Store(1, simpleProcess)
      ))
    );
    
    parProcess.production("parProcess", ActionFetch.fetch0, 1, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenDelim('(', scanner)),
        new Store(0, process),
        new Terminal(new TokenDelim(')', scanner))
      ))
    );      

    optDotSimpleProcess.production("optDotSimpleProcess", ActionFetch.fetch0, 1, 0,
      new Choice(new GrammarList(
        new Sequence(new GrammarList(
          new Terminal(new TokenDelim('.', scanner)),	
          new Store(0, simpleProcess)
        )),
        new Store(0, nullProcess)
      ))
    );

    ask.production("ask", new ActionAsk(), 2, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("ask", scanner)),
        new Store(0, new TerminalFamily(new TokenIde(""))),
        new Store(1, optDotSimpleProcess)
      ))
    );

    say.production("say", new ActionSay(), 2, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("say", scanner)),
        new Store(0, term),
        new Store(1, optDotSimpleProcess)
      ))
    );

    be.production("be", new ActionBe(), 2, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("be", scanner)),
        new Store(0, term),
        new Store(1, optDotSimpleProcess)
      ))
    );

    wait.production("wait", new ActionWait(), 2, 0,
      new Sequence(new GrammarList(
        new Terminal(new TokenKey("wait", scanner)),
        new Store(0, term),
        new Store(1, optDotSimpleProcess)
      ))
    );
    
    return root;   
  }
}

class UserException extends SynexException {
  public UserException(String msg) {
    super(msg);
  }
}

class ActionLet extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return 
      new CodeLet(
        ((TokenIde)parser.fetch(0)).ide, 
        (IdeList)parser.fetch(1), 
        (CodeProc)parser.fetch(2), 
        (CodeProc)parser.fetch(3), 
        beg, end);
  }
}

class ActionTopFocus extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeTopFocus(((TokenIde)parser.fetch(0)).ide, beg, end);
  }
}

class ActionIde extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeIde(((TokenIde)outcome).ide, beg, end);
  }
}

class ActionIdeList extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    if (parser.fetch(0) == null) {
      return null;
    } else {
      return new IdeList(((TokenIde)parser.fetch(0)).ide, (IdeList)parser.fetch(1), beg, end);
    }
  }
}

class ActionTermList extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    if (parser.fetch(0) == null) {
      return null;
    } else {
      return new TermList((CodeTerm)parser.fetch(0), (TermList)parser.fetch(1), beg, end);
    }
  }
}

class ActionString extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    throw new UserException("string not implemented"); // --
  }
}

class ActionReal extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeReal(((TokenReal)outcome).r, beg, end);
  }
}

class ActionInCap extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeInCap((CodeTerm)parser.fetch(0), beg, end);
  }
}

class ActionOutCap extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeOutCap((CodeTerm)parser.fetch(0), beg, end);
  }
}

class ActionOpenCap extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeOpenCap((CodeTerm)parser.fetch(0), beg, end);
  }
}

class ActionStay extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeStay(beg, end);
  }
}

class ActionRoute extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    if (parser.fetch(1) == null) {
      return parser.fetch(0);
    } else {
      return new CodeRoute((CodeTerm)parser.fetch(0), (CodeTerm)parser.fetch(1), beg, end);
    }
  }
}

class ActionParallel extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    if (parser.fetch(1) == null) {
      return parser.fetch(0);
    } else {
      return new CodeParallel((CodeProc)parser.fetch(0), (CodeProc)parser.fetch(1), beg, end);
    }
  }
}

class ActionAmbient extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeAmbient(false,
      new CodeIde(((TokenIde)parser.fetch(0)).ide, beg, end), 
      (CodeProc)parser.fetch(1), beg, end);
  }
}

class ActionLetExpansion extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeLetExpansion(((TokenIde)parser.fetch(0)).ide,
        (TermList)parser.fetch(1), (CodeTerm)parser.fetch(2), beg, end);
  }
}

class ActionProcIde extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeProcIde(((TokenIde)parser.fetch(0)).ide, beg, end);
  }
}

class ActionMarkedAmbient extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeAmbient(true,
      new CodeIde(((TokenIde)parser.fetch(0)).ide, beg, end), 
      (CodeProc)parser.fetch(1), beg, end);
  }
}

class ActionStop extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeStop(beg, end);
  }
}

class ActionImplode extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeImplode(beg, end);
  }
}

class ActionEnact extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeDo((CodeTerm)parser.fetch(0), (CodeProc)parser.fetch(1), beg, end);
  }
}

class ActionNew extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeNew(((TokenIde)parser.fetch(0)).ide, (CodeProc)parser.fetch(1), beg, end);
  }
}

class ActionRecursion extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeRecursion(((TokenIde)parser.fetch(0)).ide, (CodeProc)parser.fetch(1), beg, end);
  }
}

class ActionScream extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeScream(((TokenString)parser.fetch(0)).str, (CodeProc)parser.fetch(1), beg, end);
  }
}

class ActionAsk extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeAsk(((TokenIde)parser.fetch(0)).ide, (CodeProc)parser.fetch(1), beg, end);
  }
}

class ActionSay extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeSay((CodeTerm)parser.fetch(0), (CodeProc)parser.fetch(1), beg, end);
  }
}

class ActionBe extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeBecome((CodeTerm)parser.fetch(0), (CodeProc)parser.fetch(1), beg, end);
  }
}

class ActionWait extends Action {
  public Outcome exec(Parser parser, Outcome outcome, Location beg, Location end) throws SynexException {
    return new CodeWait((CodeTerm)parser.fetch(0), (CodeProc)parser.fetch(1), beg, end);
  }
}


