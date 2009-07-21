1. Status.
	This library supports only a few BML annotation
	types, and some BML expression types yet. It can
	load a .class file with annotations, save it,
	parse supported BML annotations or fragment of bytecode
	and display single BML annotation, single method
	or the whole class to a String.	Adding methods to
	/ removing from BCClass is not supported.

2. Testing.
	After installing this library, set proper paths in
	test.Paths class (these paths are used for tests only),
	and run test.ManualTests (it should not crash), and
	test.AutomatedTests (it should not crash and it should
	display that all tests passes).

3. Using this library.
	Create a annot.bcclass.BCClass (from JavaClass or from
	filename), it represents a bytecode class. Use it's
	getMethod(int) method to get bytecode methods, or
	getAllAttributes() to get all annotations from it.
	Annotations can be added (addAttribute method of BCClass
	or BCMethod), replaced (replace method of replaced
	annotation), parsed (parse method), or removed
	(remove method). Each BML annotation and expression have
	printCode method that returns it's string representation
	(toString is vary simplified and should be used only by
	debugger). BCClass and BCMethod have also printCode methods.
	If you don't know how to get a BMLConfig conf parameter,
	you can usually simply create a new one. Use methods from
	annot.textio.CodeFragment to find position in bytecode
	(method, instruction and annotation) at given line
	of bytecode. Use CodeFragment for parsing large fragments
	of bytecode into BCClass. Do not use BCEL's class
	nor method diffrent than in this library (you should access
	BCEL structures via BCClass, do not create new JavaClass,
	ClassGen nor MethodGen, unrelated with used BCClass).

4. Supported language:
	Attributes:
		class invariant, method specification, assert
		and loop specification.
	Expressions:
		+ - * / % - << >> | & ^ < <= > >= == != <==> <=!=> ==>
		&& || forall exists ?: . [] old
		true, false, this, null, result, arraylength,
		NumberLiteral; local, field and bound variables;
		modifyExpressions.

5. Extending supported language.
	To add a constant, BML attribute, new BML expression,
	or change display style	see update.txt file how to do it
	and which methods should be updated.

6. Performing operations on AST.
	You can walk on expression's AST. For example, to add
	desugar functionality, create a subclass of ExpressionWalker
	and pass it as a parameter of Expression.iterate
	or BCClass.iterate (it's iter(...) method will be called
	for each expression node in given order).
	annot.bcexpression.util.DesugarWalker class was created
	as a simple desugar example.
