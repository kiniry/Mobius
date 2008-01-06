package experiments;

import java.io.FileInputStream;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;

import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlFlow;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.Parser;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacFileManager;

public class Test {
	int x = 13;
	//@ invariant x > 4;
	/**
	 * @param args
	 */
	//@ requires x == 2;
	//@ensures \result == 12;
	public int a(){
		return 12;
	}
	public static void main(/*@ non_null */String[] args) throws Exception {
		//@ ghost int x = 4;
		//@ ghost int y = 5;
		//@ assert x + y < 11;
		//@ assert (x > y ? x < 2 : y > x - 3);
		//@ assert true;
		//@ non_null
		int a = 1, b =2;
		int c;
		c = a+ b;
		Context context = new Context();
		JavacFileManager.preRegister(context);
		Parser.Factory fac;
		Scanner.Factory sfac;
		Scanner sc;
        JmlSpecs.preRegister(context); // registering the specifications repository
        JmlParser.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlParsers
        JmlScanner.JmlFactory.preRegister(context); // registering a Jml-specific factory from which to generate JmlScanners
        JmlTree.Maker.preRegister(context); // registering a JML-aware factory for generating JmlTree nodes
//        JmlCompiler.preRegister(context);
        JmlEnter.preRegister(context);
        JmlResolve.preRegister(context);
        JmlMemberEnter.preRegister(context);
        JmlFlow.preRegister(context);
        JmlAttr.preRegister(context);  // registering a JML-aware type checker

		JavaCompiler compiler = JavaCompiler.instance(context);
		String fileName = ProjectDirectory.PROJECT_DIR+"\\src\\experiments\\List.java";
		JCTree e = compiler.parse(fileName);
//		int i =0;String ia ="";
//		JmlEnter.instance(context); // Needed to avoid circular dependencies in
//									// tool constructors that only occur in
//									// testing
//		sfac = Scanner.Factory.instance(context);
//		fac = Parser.Factory.instance(context);
//		sc = sfac.newScanner(getSource());
//		Parser p = fac.newParser(sc, true, true);
//		JCTree e = p.compilationUnit();
		System.out.println(e.toString());
		//ParseTreeScanner.walk(e);
		for (int i = 0 ; i < 11; i++)
			i -= 1;
	}

	public static String getSource() throws Exception {
		FileInputStream fis = new FileInputStream(ProjectDirectory.PROJECT_DIR+"\\src\\experiments\\List.java");
		byte b[] = new byte[fis.available()];
		fis.read(b);
		return new String(b);
	}
    static public class ParseTreeScanner extends JmlTreeScanner implements IJmlVisitor {
        /** The list of nodes */
        private List<JCTree> list = new LinkedList<JCTree>();;

        /** Constructs the visitor, but otherwise does nothing. */
        public ParseTreeScanner() {
        }

        /** A convenience method to walk the given tree and return the list of
         * its nodes.
         * @param tree the tree to be walked
         * @return the list of nodes in depth-first traversal order
         */
        static public List<JCTree> walk(JCTree tree) {
            ParseTreeScanner t = new ParseTreeScanner();
            t.scan(tree);
            return t.result();
        }

        /** Returns a reference to the list accumulated so far.
         * @return the accumulator list
         */
        public List<JCTree> result() { return list; }

        /** Adds a node to the internal accumulator and then calls the
         * super class method.
         */
        @Override
        public void scan(JCTree t) {
            if (t == null) return;
            System.out.println(t.getClass().getName());
            System.out.println(t.toString());
            list.add(t);
            super.scan(t);
        }
    }
    int a = 0; public void f(){String a = "";}

}
