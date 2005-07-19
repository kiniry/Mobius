import java.io.*;
import java.util.Vector;

class LightAnalyser {

    public /*@ non_null @*/ String fileName;

    LightAnalyser(/*@ non_null @*/ String fileNameOfTheory){
	this.fileName = fileNameOfTheory;
    }

    /*
     * ensures toMatch == 1 ||
     *         toMatch == 2 ||
     *         toMatch == 3 ||
     *         toMatch == 4;
     */
    public String find(int toMatch){

	String lookFor;
	StringBuffer resultSB = new StringBuffer("");
	String result = new String("");
	int bracketStack = 0;
	LineNumberReader lNR = null;

	switch(toMatch){
	case(1) :
	    lookFor = ":sorts";
	    break;
	case(2) :
	    lookFor = ":funs";
	    break;
	case(3) :
	    lookFor = ":preds";
	    break;
	case(4) :
	    lookFor = ":axioms";
	    break;
	default :
	    return result;
	}
	
	try{ lNR = new LineNumberReader(new FileReader(fileName));}
	catch(Exception e){
	    System.out.println("Error in LightAnalyser::find");
	    System.out.println(e);
	    System.exit(-1);
	}

	//@ assert lNR != null;

	String temp = new String("");
	//@ assert temp!= null;

	boolean insideString = false;
	boolean exitFromString = false;

	try{ 
	    while( lNR.ready() && exitFromString != true ){
	    
		temp = lNR.readLine();

		//@ assert temp!= null;
		
		if( temp.indexOf(lookFor) != -1 ) {
		    // the string we are looking for is inside
		    insideString = true;
		    
// 		    //++
// 		    System.out.println("String found :");
// 		    System.out.println(temp);
// 		    //++
		}

		if(insideString) {
		    bracketStack+=countBracket(temp);

		    // remove commentary
		    int firstIndex = temp.indexOf('#');

		    if( firstIndex != -1)
			temp = temp.substring(0,firstIndex);

		    resultSB.append("\n").append(temp);
		}

		if(bracketStack==0 && insideString) {
		    exitFromString = true;

		    result = resultSB.toString();
		    
		    // remove the first and last bracket of the result
		    // (and exclude what is before like :sorts
		    int firstIndex = result.indexOf('(');
		    int lastIndex = result.lastIndexOf(')');

		    result = result.substring(firstIndex+1,lastIndex);

// 		    //++
// 		    System.out.println("Exit from String");
// 		    System.out.println(temp);
// 		    //++
		}

	    }

	}

	catch(Exception e){
	    System.out.println("Error in LightAnalyser::find");
	    System.out.println(e);
	    System.exit(-1);
	}

	if( result.length() != 0 ){
	    // a result has been found, need to delete last bracket
	}
	    
	
	return result;
    }
    
    /*
     * result is initialized at zero .
     * For each '(' , result+=1
     * For each ')' , result-=1
     */
    private int countBracket(/*@ non_null @*/ String s){

// 	//++
// 	System.out.println("LightAnalyser::countBracket with s =");
// 	System.out.println(s);
// 	//++

	int bracketStack = 0;
	int stringLength = s.length();
	int i = 0;
	char charTemp = 'a';

	for( ; i <= stringLength-1; ++i){
	    
	    try{ charTemp = s.charAt(i); }
	    catch(Exception e){
		System.out.println("Error in LightAnalyser::countBracket");
		System.out.println(e);
		System.exit(-1);
	    }

	    if( charTemp=='(' )
		bracketStack+=1;
	    else if( charTemp==')' )
		bracketStack-=1;
		
	}

// 	//++
// 	System.out.println("Leaving LightAnalyser::countBracket with bracketStack =");
// 	System.out.println(bracketStack);
// 	//++

	return bracketStack;

    }

}
