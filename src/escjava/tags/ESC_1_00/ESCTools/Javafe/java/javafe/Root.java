package javafe;

import javafe.ast.*;
import javafe.parser.*;
import javafe.parser.test.*;
import javafe.tc.*;
import javafe.test.*;
import javafe.util.*;
import javafe.test.*;


class Root { 

    void reference() {

	// Force compilation of javafe.ast.*
	PrettyPrint pp;

	// Force compilation of javafe.util.*
	CorrelatedReader cis;
	CorrelatedReaderTest cist;

	// Force compilation of javafe.parser.* and javafe.parser.test.*
	TestLex tl = new javafe.parser.test.TestLex();
	TestExpr te;
	TestParse tp;  

	// Force compilation of javafe.tc.* and its test harnesses
	PrepTypeDeclaration cs;
	FlowInsensitiveChecks iv;
	Tool t;
	SrcTool st;
	LocTool l;
	Print pr = new Print();
	SuperlinksTest slt;
	DefaultVisitor dv;
	javafe.test.lex.TestLex.main(null);

    }
}
  
