import org.jmlspecs.openjml.Main;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.*;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.JmlSpecs.*;


public class Test {

static public void main(String[] args) {
    try {
	//java.io.File f = new java.io.File("A.java");
      java.io.File f = new java.io.File("/Users/evka/Documents/final_year_project/" +
      "workspace/ConsistencyChecker/tests/zoo/enclosure/Cage.java");

	System.out.println(" ---------- ONE FILE ----------");
	{
	Main m = new Main(new String[0]);
	String s = m.prettyPrint(m.parseFile(f),true);
	System.out.println(s);
	}

	System.out.println(" ---------- MULTIPLE FILES ----------");
	{
	Main m = new Main(new String[0]);
	String s = m.prettyPrint(m.parseFiles(f).get(0),true);
	System.out.println(s);
	}

	System.out.println(" ---------- PARSE AND CHECK ----------");
	{
	Main m = new Main(new String[0]);
	m.parseAndCheck(f);
	JCTree ast = m.getClassAST("zoo.enclosure.Cage");
	System.out.println(m.prettyPrint(ast,true));

	ClassSymbol sym = m.getClassSymbol("zoo.enclosure.Cage");
	System.out.println("Class: " + sym);

	PackageSymbol psym = m.getPackageSymbol("java.lang");
	System.out.println("Package: " + psym);

	for (Symbol mm: sym.members().getElements()) {
		System.out.println(mm);

		if (mm instanceof MethodSymbol) {
			JmlMethodSpecs ms = m.getSpecs((MethodSymbol)mm);
			System.out.println(m.prettyPrint(ms.cases,false,"\n"));
		} else if (mm instanceof VarSymbol) {
			FieldSpecs fs = m.getSpecs((VarSymbol)mm);
		}
	}

	}
	
    } catch (Exception e) {
	System.out.println(e);
	e.printStackTrace(System.out);
    }
}
}
