// @(#)$Id: Typing.java,v 1.44 2001/07/11 20:04:56 leavens Exp $

// Copyright (C) 1998, 1999 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.


package jml;

//LB import edu.iastate.cs.jml.checker.*;
//LB import edu.iastate.cs.jml.checker.util.Debug;
//LB import edu.iastate.cs.jml.models.*;


public class Typing {
    /* LB  
       boolean debugOn = true;

       int errors = 0;
       public String inputFile = "";
       public Adec thisEnv = EmptyDec;
       
       static final TypeAttrib IntExp = new Aexp(new Builtin("int"));
       static final Aerr Error = new Aerr("error");
       static final Adec EmptyDec = new Adec (new Api ());
       static final ModifierSet EmptyMods = new ModifierSet();
       static final TypeAttrib NoRetType = new Builtin("norettype");
       static final TypeAttrib boolExp = new Aexp(new Builtin("boolean"));
       
       public int errors() {
       return errors;
       }
	
       // *************************************************************************
       public static SubstMap listUnify(JMLValueSequence ts1, JMLValueSequence ts2)
       {
       int flag = 0;
       //System.out.println("length1 length2 " + ts1.length() + " " + ts2.length());
       if ((ts1.length() == 0) && (ts2.length() == 0))
	flag = 1;
	if ((ts1.length() == 0) && (ts2.length() > 0))
		flag = 2;
	if ((ts1.length() > 0) && (ts2.length() == 0))
		flag = 3;
	if ((ts1.length() > 0) && (ts2.length() > 0))
		flag = 4;
	switch(flag) {
		case 1: return new IdentitySubstMap();
		case 2: return null;
		case 3: return null;
		case 4: TypeAttrib t1, t2;
		        SubstMap s1 = null;
		        try {
			 t1 = (TypeAttrib)ts1.first();
			 t2 = (TypeAttrib)ts2.first();

			 //System.out.println("t1 t2 "+ t1 + " " +  t2);
			 s1 = t1.MGU(t2);
			 //System.out.println("subst s1 "+ s1);
			 if (s1 == null)
			   return null;
			 ts1 = ts1.trailer();
			 ts2 = ts2.trailer();
			} catch (Exception e) 
			  {
			    e.printStackTrace();
			  }
			JMLValueSequence ts3, ts4;
			ts3 = new JMLValueSequence();
			ts4 = new JMLValueSequence();
			//System.out.println("len ts3 ts4 "+ ts3.length() + " " + ts4.length());
			TypeAttrib t;
			Enumeration e = ts1.elements();
			while (e.hasMoreElements()) {
				t = (TypeAttrib)e.nextElement();
				ts3 = ts3.insertFront(t.apply(s1));
			}  
			e = ts2.elements();
			while (e.hasMoreElements()) {
				t = (TypeAttrib)e.nextElement();
				ts4 = ts4.insertFront(t.apply(s1));
			}  
			SubstMap s2 = Typing.listUnify(ts3,ts4);
			if (s2 == null)
				return null;
			return s2.compose(s1);
		default:
			return null;
		     }
   }   

// *************************************************************************
  public static TypeAttrib getSuper (TypeAttrib t1, TypeAttrib t2, Adec env)
  {
    if (t1 instanceof Aexp)
      t1 = ((Aexp)t1).getType();
    
    if (t1 instanceof Aloc)
      t1 = ((Aloc)t1).getType();
    
    if (t2 instanceof Aexp)
      t2 = ((Aexp)t2).getType();
    
    if (t2 instanceof Aloc)
      t2 = ((Aloc)t2).getType();
    
    if (t1.equals(t2))
      return t1;

    if (isNumericType(t1)&&isNumericType(t2)) {
	String type1 = ((Builtin)t1).getName();
	String type2 = ((Builtin)t2).getName();

	if (type1.equals("short")) {
	    if (type2.equals("byte"))
	      return t1;
	  }

	if (type2.equals("short"))
	  {
	    if (type1.equals("byte"))
	      return t2;
	  }


	return BinaryNumericPromotion(t1,t2);
      }

    if (t1 instanceof Anull)
      return t2;

    if (t2 instanceof Anull)
      return t1;

    if (t1.isAssignable(t2, Contexts.ASSIGN, env))
      return t1;

    if (t2.isAssignable(t1, Contexts.ASSIGN, env))
      return t2;

    return new Aerr("No common type between "+t1+" and "+t2);
  }

// *************************************************************************
  public static boolean isWideningPrimitiveConversion (String lhs, 
						       TypeAttrib rhstype)
    {
      if (rhstype instanceof Builtin)
	{
	  String rhs = ((Builtin)rhstype).getName();
	  //byte to short, int, long, float, or double 

	  if (lhs.equals("byte"))
	    {
	      return (rhs.equals("short")||rhs.equals("long")||rhs.equals("int")
		      ||rhs.equals("float")||rhs.equals("double"));
	    }

	  //short to int, long, float, or double 

	  if (lhs.equals("short"))
	    {
	      return (rhs.equals("long")||rhs.equals("float")||
		      rhs.equals("int")||rhs.equals("double"));
	    }
	  
	  //char to int, long, float, or double 

	  if (lhs.equals("char"))
	    {
	       return (rhs.equals("long")||rhs.equals("float")||
		       rhs.equals("int")||rhs.equals("double"));
	    }
	  
	  //int to long, float, or double 

	  if (lhs.equals("int"))
	    {
	      return (rhs.equals("long")||rhs.equals("float")||
		      rhs.equals("double"));
	    }

	  //long to float or double 
	  
	  if (lhs.equals("long"))
	    {
	      return (rhs.equals("float")||rhs.equals("double"));
	    }

	  //float to double 
	  
	  if (lhs.equals("float"))
	    {
	      return rhs.equals("double");
	    }
	}
      
      return false;
    }

// *************************************************************************
  public static TypeAttrib BinaryNumericPromotion (TypeAttrib t1, TypeAttrib t2)
    {
      if ((t1 instanceof Builtin)&&(t2 instanceof Builtin))
	{
	  String type1 = ((Builtin)t1).getName();
	  String type2 = ((Builtin)t2).getName();

	  if (type1.equals("double"))
	    return t1;

	  if (type2.equals("double"))
	    return t2;

	  if (type1.equals("float"))
	    return t1;

	  if (type2.equals("float"))
	    return t2;
	  
	  if (type1.equals("long"))
	    return t1;

	  if (type2.equals("long"))
	    return t2;
	  return new Builtin("int");
	}
      return new Aerr("Error! Can't apply Binary Numeric Promotion");
    }

// *************************************************************************
  public static TypeAttrib UnaryNumericPromotion   (TypeAttrib t1)
    {
      //byte, short, or char,
      if (t1 instanceof Builtin)
	{
	  String type = ((Builtin)t1).getName();
	  if ((type.equals("byte"))||
	      (type.equals("short"))||
	      (type.equals("char")))
	    return new Builtin("int");
	}
      return t1;
    }

    // ** is it not statically wrong (i.e., ok) to cast t2 to t1? ** 
  public static boolean isProperCast (TypeAttrib t1, TypeAttrib t2, Adec env)
  {
    return (t2 instanceof Anull) || t1.isAssignable(t2,Contexts.CAST, env);
  }

// *************************************************************************
  public static boolean isSubClass (TypeAttrib t1, String cname, Adec env)
    {
      if (t1 instanceof Aclass) {
	  if (((Aclass)t1).getName().equals(cname))
	    return true;
	  
	  TypeAttrib parent = ((Aclass)t1).getParent();
	  if (parent instanceof PlaceHolder) {
	      parent = Typing.processPlaceHolder(parent, env);
	  }
	  return isSubClass(parent,cname,env);
      }
      return false;
    }

  // *************************************************************************
  public ASTTypeAttribPair typeOfSuper(Adec env, int line, int column)
  {
      TypeAttrib t = null;
      ASTTypeAttribPair r = new ASTTypeAttribPair();
      if (env.getCurrentClass() instanceof Aclass) {
          t = ((Aclass)(env.getCurrentClass())).getParent();
          r = new ASTTypeAttribPair(new Line(line, column, "super"), 
                                    new Aexp(new Aself(t, "super")));
      } else {
          reportTypeError(line, column,
                          "super used outside of a class");
          if (env.getCurrentClass() instanceof Ainterface) {
              t = (Ainterface)(env.getCurrentClass());
              r = new ASTTypeAttribPair(new Line(line, column, "super"), 
                                        new Aexp(new Aself(t, "super")));
          }
      }
      return r;
  }

  // *************************************************************************
//      /** is t1 a subinterface of the interface named iname?
//       **
  public static boolean isSubInterface (TypeAttrib t1, String iname, Adec env)
    {
      if ((t1 != null)&&(t1 instanceof Ainterface))
	{
	  if (((Ainterface)t1).getName().equals(iname))
	    return true;
	  TypeAttrib parentList = ((Ainterface)t1).getParent();
	  if (parentList instanceof Alist)
	    {
	      Enumeration iter = ((Alist)parentList).elements();
	      while (iter.hasMoreElements())
		{
		  TypeAttrib t = (TypeAttrib)iter.nextElement();
		  if (t instanceof PlaceHolder)
		    {
//  		/*
//  		      String fqn = ((PlaceHolder)t).name;
//  		      Key id = new Key(fqn.substring(fqn.lastIndexOf('.')+1));
//  		 *
		      t = Typing.processPlaceHolder(t,env);
		    }
		  if ((t != null)&&(t instanceof Ainterface))
		    {
		      String name;
		      name = ((Ainterface)t).getName();
		      if (name.equals(iname))
			{
			  return true;
			}

		      if (isSubInterface(t,iname,env)) {
                          return true;
                      }
		    }
		}
	    }
	}
      return false;
    }

// *************************************************************************
  public static boolean isImplementedBy (TypeAttrib t1, TypeAttrib t2, Adec env)
    {
      TypeAttrib implementList = ((Aclass)t1).getImplement();

      if (implementList instanceof Alist)
	{
	  Enumeration iter = ((Alist)implementList).elements();
	  while (iter.hasMoreElements())
	    {
	      TypeAttrib t = (TypeAttrib)iter.nextElement();

              if (t instanceof PlaceHolder)
              {
		t = Typing.processPlaceHolder(t,env);
              }
	      if (t instanceof Ainterface)
		{
		  if (((Ainterface)t).getName().equals(((Ainterface)t2).getName()))
		    return true;
		  if (isSubInterface(t,((Ainterface)t2).getName(),env))
		    return true;
		}
	    }
	}
      
      TypeAttrib parent = ((Aclass)t1).getParent();
      if (parent instanceof PlaceHolder) {
          parent = Typing.processPlaceHolder(parent, env);
      }
      if (parent instanceof Aclass) {
	  return isImplementedBy(parent,t2,env);
      }
      return false;
    }
		      
	    
// *************************************************************************
  public static boolean isIntegerType (TypeAttrib t)
    {
      // byte, short, int, and long
      if (t instanceof Builtin)
	{
	  String type = ((Builtin)t).getName();
	  if ( type.equals("byte") || type.equals("int")
	      || type.equals("short") || type.equals("long")
	      || type.equals("char") )
	    return true;
	}

      return false;
    }

// *************************************************************************
  public static boolean isNumericType (TypeAttrib t)
    {
      if (isIntegerType(t))
	return true;

      if (t instanceof Builtin)
	{
	  String type = ((Builtin)t).getName();
	  if ((type.equals("float"))||(type.equals("double")))
	    return true;
	}

      return false;
    }

// *************************************************************************
  public static boolean isReferenceType (TypeAttrib t)
    {
      return  ((t instanceof Aarray)||
	       (t instanceof Aclass)||
	       (t instanceof Ainterface));
    }

   // *************************************************************************
   
    public static ModifierSet adjustModifiersForMember(ModifierSet m, Adec env)
    {
        if (env.currentClass instanceof Ainterface)
            {
                m = m.insert(Modifier.PUBLIC)
                    .difference(new ModifierSet(Modifier.DEFAULT));
            }
        return m;
    }

    public static ModifierSet adjustModifiersForMethod(ModifierSet m, Adec env)
    {
        m = adjustModifiersForMember(m, env);
        if ( env.currentClass instanceof Atype
             && env.currentClass.getClassModifiers().has(Modifier.PURE) ) {
            m = m.insert(Modifier.PURE);
        }
        return m;
    }

    public static ModifierSet adjustModifiersForField(ModifierSet m, Adec env)
    {
        m = adjustModifiersForMember(m, env);
        return m;
    }

  // *************************************************************************
  public static boolean isDefinedMethod(Key method,
					JMLValueToObjectMap methEnv,
					Adec env
					)
    {
      TypeAttrib rv1 = null;
      TypeAttrib rv2 = null;
      try {
	  rv1 = (TypeAttrib)methEnv.apply(method);
	  rv2 = (TypeAttrib)(((Api)env.getType()).getMethEnv()).apply(method);
      } catch (JMLNoSuchElementException e) {
      }
      if ((rv1 != null)&&(rv2 != null)) {
	  Ameth meth1 = null;
	  Ameth meth2 = null;
          meth1 = (Ameth)rv1;
          meth2 = (Ameth)rv2;
	  return meth2.containsWithoutModels(meth1);
      }
	  
      if (rv1 != null) {
	  if (rv1 instanceof Ameth) {
	      Enumeration iter = ((Ameth)rv1).elements();
	      while (iter.hasMoreElements()) {
		  TypeAttrib t = (TypeAttrib)iter.nextElement();
		  if (t instanceof ArrowType) {
		      if (!((ArrowType)t).getModifiers().has(Modifier.MODEL))
			return false;
		  }
	      }
	      return true;
	  }
      }
      return false;
    }

// *************************************************************************
  protected static boolean checkMethodModifiers(ArrowType rv1, ArrowType rv2,
						String currentFile,
						Aerr errorMsg, 
						boolean hasDuplicate) 
  {
      
      boolean okSoFar = true;
      ModifierSet mods1 = rv1.getModifiers();
      ModifierSet mods2 = rv2.getModifiers();
		      
       //  /* [[[The following is not right, as it doesn't deal with refinements
//            which declare a final method.  Finality should only apply
//            to subclasses, not refinements in JML.
//            So the check and output is turned off for the time
//            being to suppress incorrect error messages.]]]
//        if (mods1.has(Modifier.FINAL) && hasDuplicate) {
//  	  errorMsg.message = "Can't override a final method " + rv1.getNameToken().getText() + " on Line ";
//  	  errorMsg.message += rv1.getNameToken().line+" in "+rv1.fromClass;
//  	  errorMsg.fileName = currentFile;
//  	  errorMsg.column = rv2.getNameToken().column;
//  	  errorMsg.line = rv2.getNameToken().line;
//  	  errorMsg.reportedOnce = true;
//  	  okSoFar = false;
//        }
//         *
		      
//         /* [[[The following is not right, as it doesn't deal with refinements
//            which refine a static method.
//            So the check and output is turned off for the time
//            being to suppress incorrect error messages.]]]
//        if (okSoFar&& mods1.has(Modifier.STATIC)) {
//  	  if (!(mods2.has(Modifier.STATIC))) {
//  	      errorMsg.message = "Can't override a static method on Line ";
//  	      errorMsg.message += rv1.getNameToken().line+" in "+rv1.fromClass;
//  	      errorMsg.fileName = currentFile;
//  	      errorMsg.column = rv2.getNameToken().column;
//  	      errorMsg.line = rv2.getNameToken().line;
//  	      errorMsg.reportedOnce = true;
//  	      okSoFar = false;
//  	  }
//        }
//        if (okSoFar&& mods2.has(Modifier.STATIC)) {
//  	  errorMsg.message = "A static method can't override/implement a non-static method ";
//  	  errorMsg.message += rv1.getNameToken().line+" in "+rv1.fromClass;
//  	  errorMsg.fileName = currentFile;
//  	  errorMsg.column = rv2.getNameToken().column;
//  	  errorMsg.line = rv2.getNameToken().line;
//  	  errorMsg.reportedOnce = true;
//  	  okSoFar = false;
//        }
//         *

      if (okSoFar && mods1.has(Modifier.PUBLIC)
                  && !mods1.has(Modifier.MODEL)) {
	  if (!mods2.has(Modifier.PUBLIC)) {
	      errorMsg.message = "Can't override/implement a method to be more private; The method overriden is on Line ";
	      errorMsg.message += rv1.getNameToken().line+" in "+rv1.fromClass;
	      errorMsg.fileName = currentFile;
	      errorMsg.column = rv2.getNameToken().column;
	      errorMsg.line = rv2.getNameToken().line;
	      errorMsg.reportedOnce = true;
	      okSoFar = false;
	  }
      }
      
      if (okSoFar && mods1.has(Modifier.PROTECTED)) {
	  if (!mods2.has(Modifier.PROTECTED) && !mods2.has(Modifier.PUBLIC))
	      {
		errorMsg.message = "Can't override/implement a method to be less visible; The method overriden is on Line ";
		errorMsg.message += rv1.getNameToken().line+" in "+rv1.fromClass;
		errorMsg.fileName = currentFile;
		errorMsg.column = rv2.getNameToken().column;
		errorMsg.line = rv2.getNameToken().line;
		errorMsg.reportedOnce = true;
		okSoFar = false;
	      }
      }
		      
      if (okSoFar&& !mods1.has(Modifier.PRIVATE)) {
	  if (mods2.has(Modifier.PRIVATE)) {
	      errorMsg.message = "Can't override/implement a method to be less visible; The method overriden is on Line ";
	      errorMsg.message += rv1.getNameToken().line+" in "+rv1.fromClass;
	      errorMsg.fileName = currentFile;
	      errorMsg.line = rv2.getNameToken().line;
	      errorMsg.column = rv2.getNameToken().column;
	      errorMsg.reportedOnce = true;
	      okSoFar = false;
	  }
      }
      return okSoFar;
  }

// *************************************************************************
  public static boolean checkSignatures(ArrowType rv1, ArrowType rv2,
					Aerr errorMsg,
					boolean checkForDuplicates,
					int phase,
					String currentFile
					)   
  {
      if (phase == Contexts.PHASE2) {
	  //System.out.println("In phase "+phase+" comparing ");
	  LineAST tok = rv1.getNameToken();
	  //System.out.println("Method "+tok.text+" on Line "+tok.line+" in "+rv1.fromClass);
	  //System.out.println("and");
	  tok = rv2.getNameToken();
	  //System.out.println("Method "+tok.text+" on Line "+tok.line+" in "+rv2.fromClass);
	  
	  // this check can be done only in phase2      
	      
	  if (!rv1.hasSameReturnType(rv2)) {
	      TypeAttrib t1 = rv1.getReturnType();
	      TypeAttrib t2 = rv2.getReturnType();
	      errorMsg.message = "Method redefined with different return type:\n";
	      errorMsg.message += "definitions are:\n";
	      errorMsg.message += "Line "+rv1.getNameToken().line+" in "+rv1.fromClass;
	      errorMsg.message += " with return type:\n    "+t1;
	      errorMsg.message += "\nand\n";
	      errorMsg.message += "Line "+rv2.getNameToken().line+" in "+rv2.fromClass;
	      errorMsg.message += " with return type:\n    "+t2;
	      errorMsg.fileName = currentFile;
	      errorMsg.line = rv2.getNameToken().line;
	      errorMsg.column = rv2.getNameToken().column;
	      errorMsg.reportedOnce = true;
	      
	      return false;
	  } else {
	      // redefinition of a method
	      // System.out.println("Methods match");
	      boolean modOk =  checkMethodModifiers(rv1, rv2, 
					  currentFile, errorMsg,
					  (!checkForDuplicates));
              if (modOk) {
                  // Adding previous definitions to retrieve in Behavioral subtyping later while generating the code
                  
                   rv2.addOrigDef(rv1);
              }
              return modOk;
	  }
      }
      
      return true;
  }

// *************************************************************************
  public static Ameth insertMethodSignature( ArrowType sig1, Ameth rv2,
					     Aerr errorMsg,
					     boolean checkForDuplicates,
					     int phase,
					     String currentFile,
					     Key dv1,
					     Ameth sigList
					     )
    {
      //System.out.println("calling method with list check");
      Enumeration iter = ((Ameth)rv2).elements();
      JMLValueSequence vs = new JMLValueSequence();
      ArrowType sig2 = rv2.lookupSignature(sig1);
      if (sig2 == null) { // no matching signature
	  return sigList.insertSignature(sig1);
      } else {
	  if (checkForDuplicates) {
	      errorMsg.message = "Duplicate Definition of Method;";
	      errorMsg.message += "\ndefinitions are:\n";
	      errorMsg.message += "Line "+sig1.getNameToken().line
		  +" in "+sig1.fromClass;
	      errorMsg.message += "\nand\n";
	      errorMsg.message += "Line "+sig2.getNameToken().line
		  +" in "+sig2.fromClass;
	      errorMsg.reportedOnce = true;
	  } else {
	      checkSignatures(sig1,sig2,errorMsg, 
			      checkForDuplicates,phase,currentFile);
	  }
	  return sigList;
      }
      
    }
	    

// *************************************************************************
  public static Ameth unionMethodSignatures(Ameth rv1, Ameth rv2,
					    Aerr errorMsg,
					    boolean checkForDuplicates,
					    int phase,
					    String currentFile,
					    Key dv1)
    {
      //System.out.println("calling list with list check");
      Enumeration iter1 = ((Ameth)rv1).elements();
      Ameth sigList = rv2;
      while (iter1.hasMoreElements()) {
	  boolean errorflag = true;
	  TypeAttrib sig1 = (TypeAttrib)iter1.nextElement();
	  if (sig1 instanceof ArrowType) {
	      sigList = insertMethodSignature ((ArrowType)sig1,rv2,
					       errorMsg,checkForDuplicates,
					       phase,currentFile,dv1,
					       sigList);
	  }
      }
	      
      return sigList;
    }

// *************************************************************************
  public static TypeAttrib getCheckedAttribStatic(Adec env,
						  TypeAttrib obtained,
						  ModifierSet modifiers,
						  boolean isLoc)
    {
      if (obtained.fromClass instanceof Ainterface)
	return obtained;

      String obtainedClassName = obtained.getFromClassName();
      String currentClassName = env.currentClass.getName();
      // String currentClassName = env.currentClass.getFromClassName();

      boolean accessAllowed = false;
      if (modifiers.has(Modifier.PRIVATE))
	{
          //   obtained = the name whose access is being checked.
//               env.currentClass = the class in whose scope we are
//               If obtained is declared private, then it is allowed to be
//                 accessed if

//                 (a) if 'obtained' refers to the class that we are in, as in
//                           private class I {
//                                I i = new I();
//                           }
//                      (and check the above when I is an inner class).
//                 (b) the class that declares the name whose access
//                 is being checked is the class in whose scope we are
//                 [ env.currentClass.getName().equals(obtained.getFromClassName() ) ]
//                 as in
//                           class Outer {
//                                private int i;
//                                private int j = i;
//                                private class I {}
//                                private I ii = new I();
//                           }
//                 (c) the class that declares the name whose access is being
//                 checked is a parent scope.
          
      if (!currentClassName.equals(obtainedClassName) &&
        !((obtained instanceof Aclass) &&
            obtained.getName().equals(currentClassName)) &&
          !(currentClassName.startsWith(obtainedClassName) &&
            currentClassName.length() > obtainedClassName.length() &&
            currentClassName.charAt(obtainedClassName.length()) == '.'))
        {
                if (!(modifiers.has(Modifier.SPEC_PUBLIC)
		      || modifiers.has(Modifier.SPEC_PROTECTED)))
                    return new Aerr("Access denied as member is private");
	    }
	  accessAllowed = true;
	}
      
      if ((!accessAllowed) && (modifiers.has(Modifier.PROTECTED)
                               || modifiers.has(Modifier.SPEC_PROTECTED)))
	{
	  if (!(currentClassName.equals(obtainedClassName)))
	    {
	      if (env.currentClass instanceof Ainterface)
		{
		  if (Typing.isSubInterface(env.currentClass,obtainedClassName,env))
		    {
		      return obtained;
		    }
		}
	      if (env.currentClass instanceof Aclass)
		{
		  if (Typing.isSubClass(env.currentClass,obtainedClassName,env))
		    {
		      return obtained;
		    }
		}
	    }
	}

      if ((!accessAllowed) && (modifiers.has(Modifier.PUBLIC)
                               || modifiers.has(Modifier.SPEC_PUBLIC)))
	{
	  accessAllowed = true;
	}
      
      if (!accessAllowed)
	{
	  if (!(env.currentPackage.equals(obtained.packageName)))
	    {
	      if (obtained.packageName.equals(""))
		{
		  Search s = new Search(obtained.getFromClassName(),false);
		  File f = s.result();
                  if (f != null)
		    {
		      if (!(f.getName().equals("./"+obtained.getFromClassName())))
			{
			  return new Aerr("Cant access non public members from package "+obtained.packageName);
			}
		    }
                  else
		    return new Aerr("Cant access non public members from package "+obtained.packageName);
		  
		}
	      else
		return new Aerr("Cant access non public members from package "+obtained.packageName);
	    }
	  accessAllowed = true;
	}

      return obtained;
    }

// *************************************************************************
  public static TypeAttrib processPlaceHolder (TypeAttrib holder, Adec env)
  {
      TypeAttrib result = holder;
      Aloc location = null;

      if (result instanceof Aloc) {
	  location = (Aloc)result;
	  result = location.getType();
      }
      if (result instanceof PlaceHolder) {
	  PlaceHolder p = (PlaceHolder)result;
	      
	  if (p.isResolved()) {
	      result = p.type;
	  } else {
	      result = new Aunknown(p.getName());
	      PackageEnv penv = (PackageEnv)env.getParentEnv();
	      try {
		  String newname = p.getName();
		    
		  result = (TypeAttrib)penv.lookup(new Key(newname));
		  if (location != null) {
		      location.setType(result);
		      result = location;
		  }
		  if (!(result instanceof PlaceHolder)) {
		      return result;
		  }
	      } catch (Exception e) {}
	      File f = new File(p.filename);
	      if (!f.exists()) {
		  Search s = new Search(p.name, false);
		  f = s.result();
	      }
	      if (f != null) {

		  String pkg = JmlChecking.getPackageName(p.name);
		  boolean imported = !env.packageName.equals(pkg);
		  String standardPath = 
		      JmlChecking.standardizeFileName(f.getAbsolutePath());
                  Adec dec = null;
                  try {
                      dec = JmlChecking.runNameResolution(f, standardPath,
                                                          imported);
                  } catch (java.io.IOException e) {
		    result = new Aerr("cannot read " + e.getMessage());
                    return result;
                  }
		  JMLValueToObjectMap map = JmlChecking.getClassEnv(dec);

		  try {
		      String name = p.uname;
		      StringTokenizer st = new StringTokenizer(name,".");
		      JMLValueToObjectMap tempMap = map;
		      while (st.hasMoreTokens()) {
			  String ss = st.nextToken();
			  result = (TypeAttrib)tempMap.apply(new Key(ss));
			  if (result instanceof Atype) {
			      Adec tempDec = (Adec)((Atype)result).getEnv();
			      tempMap = ((Api)tempDec.getType()).getClassEnv();
			  } else {
			      result = new Aunknown(p.uname);
			      break;
			  }
		      }
		      if (result instanceof Atype) {
			  ModifierSet mods = ((Atype)result).getClassModifiers();
			  if (mods.has(Modifier.PRIVATE)) {
			      result = new Aerr("Can't Access private classes/interfaces");
			  }
			      
			  if (!mods.has(Modifier.PUBLIC) && !mods.has(Modifier.SPEC_PUBLIC)) {
			      if (!env.currentPackage.equals(result.packageName)) {
				  if (result.packageName.equals("")) {
				      if (!(f.getName().equals("."+File.separator+p.name))) {
					  result = new Aerr("Can't access non public classes/interfaces from a different package");
				      }
				  } else {
				      result = new Aerr("Can't access non public classes/interfaces from a different package");
				  }
			      }
			  }
		      }
		      String newname = p.getName();
		      // penv.packageMap = penv.packageMap.extend(new Key(newname),result);
		  } catch (Exception e) { 
		      result = new Aunknown(p.uname); 
		  }
	      }
	  }
      }
      
      if (location != null) {
	  location.setType(result);
	  result = location;
      }
      return result;
  }

  // *************************************************************************
  public void checkAccessibility(String varName, 
				 ModifierSet varMods,
				 ModifierSet specMods,
				 Line ln)
  {
      //
      // System.out.println("Checking accessibility for " + varName
      // + " with varMods = " + varMods
      // + " specMods = " + specMods + " line = " + ln);
      //
      // Local variables, and quantified variables, don't have *any* modifiers;
      // so have to check for what shouldn't be there, not what isn't there.
      if ( specMods.has(Modifier.PUBLIC)
           && ( varMods.has(Modifier.PRIVATE)
               || varMods.has(Modifier.PROTECTED)
               || varMods.has(Modifier.DEFAULT) )
	   && !varMods.has (Modifier.SPEC_PUBLIC) ) {
	reportTypeError(ln.line, ln.column, 
			varModifier(varMods) + " identifier '" + varName
			+ "' cannot be used in public specification");
      }
      if ( specMods.has(Modifier.PROTECTED)
           && ( varMods.has(Modifier.PRIVATE)
               || varMods.has(Modifier.DEFAULT))
	   && !( varMods.has(Modifier.SPEC_PUBLIC)
	        || varMods.has(Modifier.SPEC_PROTECTED) ) ) {
	reportTypeError(ln.line, ln.column, 
			varModifier(varMods) + " identifier '" + varName
			+ "' cannot be used in protected specification");
      }
      if (specMods.has(Modifier.DEFAULT)
	  && varMods.has(Modifier.PRIVATE)
	  && !( varMods.has(Modifier.SPEC_PUBLIC)
	        || varMods.has(Modifier.SPEC_PROTECTED) ) ) {
	reportTypeError(ln.line, ln.column, 
			varModifier(varMods) + " identifier '" + varName
			+ "' cannot be used in default privacy specification");
      }
  }

  private static String varModifier(ModifierSet varMods) {
      if (varMods.has(Modifier.PRIVATE)) {
          return "Private";
      } else if (varMods.has(Modifier.PROTECTED)) {
          return "Protected";
      } else if (varMods.has(Modifier.PUBLIC)) {
          return "Public";
      } else {
          return "Default privacy";
       }
       }
  LB */
  public static ModifierSet defaultPrivacyModifiers(ModifierSet r) {
      if (!(r.has(Modifier.PUBLIC)
            || r.has(Modifier.PROTECTED)
            || r.has(Modifier.PRIVATE))) {
          r = r.insert(Modifier.DEFAULT);
      }
      return r;
  }
    /*LB
  // *************************************************************************
  public static boolean maximallySpecific (ArrowType atype, 
					   Vector arrowtypes, Adec thisEnv)
  {
    for (int i=0; i<arrowtypes.size(); i++) {
	ArrowType anothertype = (ArrowType)arrowtypes.elementAt(i);
	if (anothertype != atype) {
	    if (!(anothertype.convertable(atype,thisEnv))) {
	        return false;
	    }
	}
    }
    return true;
  }

// *************************************************************************
  public Adec getNewEnv (ASTTypeAttribPair typAttr, Adec env, Adec thisEnv)
  {
      TypeAttrib theType = typAttr.type;
    
      if (theType instanceof Aexp) {
          theType = ((Aexp)theType).getType();
      }

	  // theType can either be a Alist or it can be a proper type
      if (theType instanceof Alist) {
          Enumeration iter = ((Alist)theType).elements();
	  while (iter.hasMoreElements()) {
	      theType = (TypeAttrib)iter.nextElement();
	      if (theType instanceof Aloc) {
		  theType = ((Aloc)theType).getType();
	      }
              if (theType instanceof Atype) {
                  break;
              }
	  }
      } else if (theType instanceof Aloc) {
	  theType = ((Aloc)theType).getType();
      }

      Adec newenv = null;
    
      theType = Typing.processPlaceHolder(theType, thisEnv);

      if (theType instanceof Aclass) {
	  theType = ((Aclass)theType).getAllEnv(env,Contexts.PHASE2);
	
	  if (theType instanceof Adec) {
	      newenv = (Adec)theType;
	      newenv.currentClass = env.currentClass;
	      newenv.currentMethod = env.currentMethod;
	      newenv.currentFile = env.currentFile;
	      newenv.currentPackage = env.currentPackage;
	  }
      } else if (theType instanceof Ainterface) {
	  theType = ((Ainterface)theType).getAllEnv(env,Contexts.PHASE2);
	  if (theType instanceof Adec) {
	      newenv = (Adec)theType;
	      newenv.currentClass = env.currentClass;
	      newenv.currentMethod = env.currentMethod;
	      newenv.currentFile = env.currentFile;
	      newenv.currentPackage = env.currentPackage;
	  }
      } else {
	  reportTypeError(typAttr.info.line, typAttr.info.column, 
			  "Dot operation not supported on " + theType);
      }
      return newenv;
  }

// *************************************************************************
  public ArrowType findConstructor(Alist argTypes, Aclass t,
				   Adec env, Adec thisEnv, 
				   Line ln)
	// check in the method list if a constructor taking those 
	// argument types is present.
  {
    if (argTypes != null) {
	if (argTypes.length() == 0) {
		// no need to declare the default constructor.
	    return null;
	}
	Adec classEnv = (Adec)t.getEnv();
	JMLValueToObjectMap methEnv = ((Api)classEnv.getType()).getMethEnv();

	TypeAttrib rv;
        String cname = t.getName();
        String name = cname.substring(cname.lastIndexOf('.')+1);
	try {
	    rv = (TypeAttrib)methEnv.apply(new Key(name));
	} 
	catch (Exception exc) {
	    reportTypeError(ln.line, ln.column, "No such constructor " + name);
	    return null;
	}
	if (rv instanceof Ameth) {
	    Aerr errorMsg = new Aerr("");
	    errorMsg.line = ln.line;
	    errorMsg.column = ln.column;
	    
	    ArrowType rt = findBestFit((Ameth)rv, argTypes, env, thisEnv, 
					errorMsg, true);
	    if (errorMsg.reportedOnce) {
		reportTypeError(errorMsg);
	    } 
	    return rt;
	} 
        else {
		// should not happen.
	    reportTypeError(ln.line, ln.column, "No such constructor " + rv);
	    return null;
	}
    }
    return null;
  }

// *************************************************************************
  public ArrowType findMethod(Alist argTypes, TypeAttrib meth,
			      Adec env, Adec thisEnv, 
			      Line ln)
	// check in the method list if a method taking those 
	// argument types is present.
  {
    if (argTypes != null) {
	TypeAttrib origMeths = meth;
	if (meth instanceof Alist) {
	    Enumeration types = ((Alist)meth).elements();
	    while (types.hasMoreElements()) {
		meth = (TypeAttrib)types.nextElement();
		if (meth instanceof Ameth) {
		    break;
		}
	    }
	}
        if (meth instanceof Ameth) {
	    Aerr errorMsg = new Aerr("");
	    errorMsg.line = ln.line;
	    errorMsg.column = ln.column;

	    ArrowType rt = findBestFit((Ameth)meth, argTypes, env, thisEnv,
				       errorMsg, false);
	    if (errorMsg.reportedOnce) {
		reportTypeError(errorMsg);
	    } 
	    return rt;
	} else {
	    reportTypeError(ln.line, ln.column, 
			    "No such method in this scope; possible types "
			    + origMeths);
	    return null;
	}
    }
    return null;
  }
	      
// *************************************************************************
  public ArrowType findBestFit (Ameth methList, Alist argTypes, 
				Adec env, Adec thisEnv, 
				Aerr errorMsg,
				boolean isConstructor)
  {
      Aerr dummyErr = new Aerr(""); // no errors recorded here are reported!

    boolean foundOne = false;
    Enumeration iter = methList.elements();
    Vector arrowtypes = new Vector(1);
    int numberOfMatchingMethods = 0;
    while (iter.hasMoreElements()) {
	TypeAttrib methType = (TypeAttrib)iter.nextElement();
	if (methType instanceof ArrowType) {
	    boolean hasReturnType =
		!((ArrowType)methType).getReturnType().equals(NoRetType);
	    if (isConstructor) {
		if (!hasReturnType
		    && matchingArgs((ArrowType)methType, argTypes, env, 
				    thisEnv, dummyErr)) {
		    arrowtypes.addElement(methType);
		    numberOfMatchingMethods++;
		}
	    } else {
		if (hasReturnType
		    && matchingArgs((ArrowType)methType, argTypes, env, 
				    thisEnv, dummyErr)) {
		    arrowtypes.addElement(methType);
		    numberOfMatchingMethods++;
		}
	    }
	}
    }


    if (numberOfMatchingMethods == 1) {
	ArrowType obtained = (ArrowType)arrowtypes.elementAt(0);
	ArrowType rt = (ArrowType)arrowtypes.elementAt(0);
	return rt;
    }

    if (numberOfMatchingMethods == 0) {
	if (methList.length() == 1) {
	    errorMsg.message = dummyErr.message;
	    errorMsg.reportedOnce = true;
	    return null;
	} else if (isConstructor) {
	    if (argTypes.length() != 0) {
		errorMsg.message = "No such constructor found in class "
				   + env.getCurrentClass();
		errorMsg.reportedOnce = true;
	    }
	    return null;
	} else {
	    errorMsg.message = methList.getName()
			       + ": No such method found in class "
			       + env.getCurrentClass();
	    errorMsg.reportedOnce = true;
	    return null;
	}
    }

    ArrowType foundMethod = null;
    for (int i=0; i<numberOfMatchingMethods; i++) {
	ArrowType currentMethod = (ArrowType)arrowtypes.elementAt(i);
	if (maximallySpecific(currentMethod, arrowtypes, thisEnv)) {
	    if (foundMethod != null) {
		errorMsg.message  = "method call is ambiguous;";
                errorMsg.message  += "possible candidates are:\n";
	        errorMsg.message  += "Line "+currentMethod.getNameToken().line+
			" in "+currentMethod.fromClass;
		errorMsg.message  += "\nand\n";
		errorMsg.message  += "Line "+foundMethod.getNameToken().line+
			" in "+foundMethod.fromClass;
		errorMsg.reportedOnce = true;
		return null;
	    }
	    foundMethod = currentMethod;
	}	
    }	
    return foundMethod;
  }

// *************************************************************************
  public boolean matchingArgs (ArrowType methtype, Alist argTypes, 
			       Adec env, Adec thisEnv, 
			       Aerr errorMsg)
  {
    boolean argsMatch = true;
	//  /*
//  	ArrowType obtained = (ArrowType)methtype;
//  	TypeAttrib res = Adec.getCheckedAttribStatic(env,
//  						     obtained,
//  						     obtained.getModifiers(),
//  						     false);
//  	if (res instanceof Aerr)
//  	  {
//  	    reportTypeError(env.currentFile,info.line,info.column,
//  			    ((Aerr)res).message);
	  
//  	  }
//  	*

    Alist formals = (Alist)methtype.getFormalEnv();
    int size1 = formals.length();
    Enumeration iter1 = formals.elements();

    int size2 = argTypes.length();
    Enumeration iter2 = argTypes.elements();

    if (size1 != size2) {
	errorMsg.message = "Improper number of arguments, expected "
	                   + size1 + " got " + size2;
	errorMsg.reportedOnce = true;
	argsMatch = false;
    } else {
	int argNum = 0;
	while (iter1.hasMoreElements()) {
	    argNum++;
	    JMLValueObjectPair vop1 = (JMLValueObjectPair)iter1.nextElement();
	    TypeAttrib t1 = (TypeAttrib)vop1.value;
            t1 = Typing.processPlaceHolder(t1, thisEnv);
	    ASTTypeAttribPair e2 = (ASTTypeAttribPair)iter2.nextElement();
	    
	    TypeAttrib t2 = e2.type;

	    if (!(t1 instanceof Aloc)) {
		errorMsg.message = "Must be a location type, got " + t1;
		errorMsg.line = e2.info.line;
		errorMsg.column = e2.info.column;
		errorMsg.reportedOnce = true;
		argsMatch = false;
	    }

	    Line line = new Line(e2.info.line, e2.info.column);
	    ASTTypeAttribPair pair = new ASTTypeAttribPair(line, t2);
	    t2 = getExpressionType(pair, thisEnv, EmptyMods);

	    if (t2 instanceof Aexp) {
		t2 = ((Aexp)t2).getType();
	    }
	    if (t2 instanceof Aloc) {
		t2 = ((Aloc)t2).getType();
	    }
	    if (!t1.isAssignable(t2, Contexts.METHOD,thisEnv)) {
		errorMsg.message += 
		    "\nArgument " + argNum + " '" + t2 
		    + "' does not match formal parameter '" + t1 + "'";
		errorMsg.line = e2.info.line;
		errorMsg.column = e2.info.column;
		errorMsg.reportedOnce = true;
		argsMatch = false;
	    }
	}
    }
    return argsMatch;
  }
  
// *************************************************************************
  public TypeAttrib getExpressionType (ASTTypeAttribPair pair, 
				       Adec thisEnv,
				       ModifierSet specMods)
  {
      TypeAttrib typ = pair.type;
      TypeAttrib result = typ;
      if (typ instanceof Aexp) {
	  typ = ((Aexp)typ).getType();
          result = typ;
      }
      if (typ instanceof Alist) {
	  Enumeration types = ((Alist)typ).elements();
	  while (types.hasMoreElements()) {
	      TypeAttrib t1 = (TypeAttrib)types.nextElement();
	      if (t1 instanceof Builtin) {
		  result = t1;
	      }
	      if (t1 instanceof Aloc) {
		  t1 = Typing.processPlaceHolder(t1, thisEnv);

		  ModifierSet mods = ((MTypeAttrib) t1).getModifiers();

		     // The following has been added to make 
		     // sure that a public specification does not refer 
		     // to private variables, etc. 

		  checkAccessibility(pair.info.name, mods,
				     specMods, pair.info);
		  result = t1;
	      }
	  }
      }
      if (typ instanceof PlaceHolder) {
	  result = Typing.processPlaceHolder(typ, thisEnv);
      }
      return result;
  }

// *************************************************************************
  // [[[NOTE: Size of initializer is not checked.]]]
  public boolean initializerRightSizeAndType (int dims,
                                              TypeAttrib t,
                                              TypeAttrib elementtype)
  {
      //System.out.println("INITIALIZER " + t + " " + dims + " " + elementtype);
      if (t == null) {
          return true;
      }
      TypeAttrib temptype = t;
      if (temptype instanceof Aexp) {
          temptype = ((Aexp)temptype).getType();
      }
      if (dims == 0) {
       //   /* Here t should be an item which is consistent with
//                  elementType.  Note that some items might be a 1-element
//                  Alist.
//          *
          try {
              if (temptype instanceof Alist) {
                  Alist temptypeAsAlist = (Alist)temptype;
                  if (temptypeAsAlist.length() == 1) {
                      temptype = (TypeAttrib)(temptypeAsAlist.subTerms()
                                              .itemAt(0));
                  }
              }
              TypeAttrib t1 = temptype;
              if (t1 instanceof Aexp) {
                  t1 = ((Aexp)t1).getType();
              }
              if (t1 instanceof Aloc) {
                  t1 = ((Aloc)t1).getType();
              }
              if (!(elementtype.isAssignable(t1, Contexts.ASSIGN, thisEnv))) {
                return false;
              }
          } catch (Exception e) {
              return false;
          }
      } else { // dims > 0
        //  /* Here t should be a list of items each of which is an array of
//                  dimension dims and basic type elementType.
//          *
          try {
              Enumeration iter = ((Alist)temptype).elements();
              while (iter.hasMoreElements()) {
                  TypeAttrib t1 = (TypeAttrib)iter.nextElement();
                  if (!initializerRightSizeAndType(dims-1, t1, elementtype)) {
                        return false;
                  }
              }
          } catch (Exception e) {
              return false;
          }
      }
      return true;
  }

// *************************************************************************
  public void checkArrayTypes (LineAST a, 
			       TypeAttrib t, Alist listoftypes)
  {
      if (!(t instanceof Aloc)) {
	  reportTypeError(a.line,a.column,"Must be a location type, got "+t);
      } else {
	  //extract the types from listoftypes
	  //check the type of array on the left ..
	  //for each type inside there must be a recurring valuesequence of
	  //size dims.

	  t = ((Aloc)t).getType();
	  if (t instanceof Aarray) {
	      int dims = ((Aarray)t).getDimensions();
	      TypeAttrib elementtype = ((Aarray)t).getType();

	      Enumeration iter = listoftypes.elements();
	      while (iter.hasMoreElements()) {
		  TypeAttrib t1 = (TypeAttrib)iter.nextElement();
		  if (!(initializerRightSizeAndType(dims-1, t1, elementtype))) {
		      reportTypeError(a.line,a.column,
				      "Can't Assign "+t1+" to "+elementtype);
		  }
	      }
	  } else {
	      reportTypeError(a.line,a.column,
			      "left hand side must be an array type "+t);
	  }
      }
  }

// *************************************************************************
  public ASTTypeAttribPair typeCheckIncDec (ASTTypeAttribPair e1, 
					    ModifierSet specMods,
					    LineAST l)
  {
      boolean flag = true;
      if (e1.type instanceof Aexp)
	{
	  e1.type = getExpressionType(e1, thisEnv, specMods);
	  if (!(e1.type instanceof Aloc))
	    {
	      reportTypeError(e1.info.line,e1.info.column,
			      "Type of operation "+l.getText()
			      +" must be a location "+e1.type);
	    }
	} 

      TypeAttrib t1 = e1.type;
      
      if (t1 instanceof Aexp) {
	t1 = ((Aexp)t1).getType();
      }
      
      if (t1 instanceof Aloc) {
	t1 = ((Aloc)t1).getType();
      }

      if (!(Typing.isNumericType(t1))) {
	  reportTypeError(e1.info.line,e1.info.column,
			  "Can't perform "+l.getText()+" operation on "+t1);
	  flag = false;
	} 
      Line line = new Line(l.line,l.column);
      return new ASTTypeAttribPair(line,e1.type);
  }

// *************************************************************************
  public ASTTypeAttribPair typeCheckUnaryOps (ASTTypeAttribPair e1, 
					      ModifierSet specMods,
					      LineAST l)
  {
      boolean flag = true;


      e1.type = getExpressionType(e1, thisEnv, specMods);

      TypeAttrib t1 = e1.type;      

      if (t1 instanceof Aexp)
	t1 = ((Aexp)t1).getType();
      
      if (t1 instanceof Aloc)
	t1 = ((Aloc)t1).getType();
      
      Line line = new Line(l.line,l.column);

      if (l.getText().equals("-")) {
	  if (Typing.isNumericType(t1)) {
	      TypeAttrib result = Typing.UnaryNumericPromotion(t1);
	      return new ASTTypeAttribPair(line,new Aexp(result));
	  } else {
	      reportTypeError(e1.info.line,e1.info.column,
			      "Can't perform unary minus operation on "+t1);
	      return new ASTTypeAttribPair(line,IntExp);
	  }
      } else {
	  if (Typing.isIntegerType(t1)) {
	      TypeAttrib result = Typing.UnaryNumericPromotion(t1);
	      return new ASTTypeAttribPair(line,new Aexp(result));
	  } else {
	      reportTypeError(e1.info.line,e1.info.column,
			      "Can't perform "+l.getText()+" operation on "+t1);
	      return new ASTTypeAttribPair(line,IntExp);
	  }
	}
  }

// *************************************************************************
  public ASTTypeAttribPair typeCheckMultiOps (ASTTypeAttribPair e1,
					      ASTTypeAttribPair e2,
					      ModifierSet specMods,
					      LineAST l, boolean assign_flag)
  {
      
      boolean flag1 = true, flag2 = true;

      e1.type = getExpressionType(e1, thisEnv, specMods);
      e2.type = getExpressionType(e2, thisEnv, specMods);

      TypeAttrib t1 = e1.type;
      TypeAttrib t2 = e2.type;
      
      if (t1 instanceof Aexp)
	t1 = ((Aexp)t1).getType();
      
      if (t1 instanceof Aloc)
	t1 = ((Aloc)t1).getType();
      
      if (t2 instanceof Aexp)
	t2 = ((Aexp)t2).getType();
      
      if (t2 instanceof Aloc)
	t2 = ((Aloc)t2).getType();

      Line line = new Line(l.line,l.column);

      if (!(Typing.isNumericType(t1)))
	{
	  reportTypeError(e1.info.line,e1.info.column,
			  "Can't perform "+l.getText()+" operation on "+t1);
	  flag1 = false;
	}
      
      if (!(Typing.isNumericType(t2)))
	{
	  reportTypeError(e2.info.line,e2.info.column,
			  "Can't perform "+l.getText()+" operation on "+t2);
	  flag2 = false;
	}
      
      if (assign_flag)
	{
	  if (e1.type instanceof Aexp)
	    {
	      if (!(((Aexp)e1.type).getType() instanceof Aloc))
		{
		  reportTypeError(e1.info.line,e1.info.column,
		      "Type of "+l.getText() + " operation must be a location "
		      +((Aexp)e1.type).getType());
		}
	    }    
	}
      
      if ((flag1)&&(flag2))
	{
	  TypeAttrib result = Typing.BinaryNumericPromotion(t1,t2);
	  return new ASTTypeAttribPair(line,new Aexp(result));
	}
      
      return new ASTTypeAttribPair(line,IntExp);
  }

// *************************************************************************
  public ASTTypeAttribPair typeCheckEqualityOps (ASTTypeAttribPair e1,
						 ASTTypeAttribPair e2,
						 ModifierSet specMods,
						 LineAST l)
  {
      boolean flag = true;
      
      e1.type = getExpressionType(e1, thisEnv, specMods);
      e2.type = getExpressionType(e2, thisEnv, specMods);

      TypeAttrib t1 = e1.type;
      TypeAttrib t2 = e2.type;
      
      if (t1 instanceof Aexp)
	t1 = ((Aexp)t1).getType();
      
      if (t1 instanceof Aloc)
	t1 = ((Aloc)t1).getType();
      
      if (t2 instanceof Aexp)
	t2 = ((Aexp)t2).getType();
      
      if (t2 instanceof Aloc)
	t2 = ((Aloc)t2).getType();

      Line line = new Line(l.line,l.column);

      if ((Typing.isIntegerType(t1))&&(Typing.isIntegerType(t2)))
	{
	  return new ASTTypeAttribPair(line, boolExp);
	}
      else
	{
	  if ((t1.equals(new Builtin("boolean")))&&(t2.equals(new Builtin("boolean"))))
	    {
	      return new ASTTypeAttribPair(line,boolExp);
	    }
	  else
	    {
	      boolean result = Typing.isProperCast(t1, t2, thisEnv);
	      if (!result)
		{
		  result = Typing.isProperCast(t2, t1, thisEnv);
		  if (!result)
		    {
		      reportTypeError(l.line,l.column,
			  "Types on both sides of "+l.getText()
			  +" do not have similar types "+t1 + " and "+ t2);
		    }
		}
	    }
	}
      return new ASTTypeAttribPair(line,boolExp);
  }
  
// *************************************************************************
  public ASTTypeAttribPair typeCheckBitwiseOps (ASTTypeAttribPair e1,
						ASTTypeAttribPair e2,
						ModifierSet specMods,
						LineAST l, 
						boolean assign_flag)
  {
      boolean flag = true;
      
      e1.type = getExpressionType(e1, thisEnv, specMods);
      e2.type = getExpressionType(e2, thisEnv, specMods);
      TypeAttrib t1 = e1.type;
      TypeAttrib t2 = e2.type;
      
      if (t1 instanceof Aexp)
	t1 = ((Aexp)t1).getType();
      
      if (t1 instanceof Aloc)
	t1 = ((Aloc)t1).getType();
      
      if (t2 instanceof Aexp)
	t2 = ((Aexp)t2).getType();
      
      if (t2 instanceof Aloc)
	t2 = ((Aloc)t2).getType();

      Line line = new Line(l.line,l.column);

      if ((Typing.isIntegerType(t1))&&(Typing.isIntegerType(t2)))
	{
	  TypeAttrib result = Typing.BinaryNumericPromotion(t1,t2);
	  return new ASTTypeAttribPair(line,new Aexp(result));
	}
      else
	{
	  if ((t1.equals(new Builtin("boolean")))&&(t2.equals(new Builtin("boolean"))))
	    {
	      return new ASTTypeAttribPair(line,boolExp);
	    }
	}

      if (assign_flag)
      {
	if (e1.type instanceof Aexp)
	  {
	    if (!(((Aexp)e1.type).getType() instanceof Aloc))
	      {
		reportTypeError(e1.info.line,e1.info.column,
		    "Type of "+l.getText()+ " operation must be a location "
		    +((Aexp)e1.type).getType());
	      }
	  }    
      }
      
      reportTypeError(l.line,l.column,
		      "Operands do not have the right types for "
		      +l.getText()+" operation "+t1+" and "+t2);
      return new ASTTypeAttribPair(line,boolExp);
  }

// *************************************************************************
  public ASTTypeAttribPair typeCheckShiftOps (ASTTypeAttribPair e1, 
					      ASTTypeAttribPair e2,
					      ModifierSet specMods,
					      LineAST l, 
					      boolean assign_flag)
  {
    boolean flag = true;
    e1.type = getExpressionType(e1, thisEnv, specMods);
    e2.type = getExpressionType(e2, thisEnv, specMods);
    TypeAttrib t1 = e1.type;
    TypeAttrib t2 = e2.type;

    if (t1 instanceof Aexp)
      t1 = ((Aexp)t1).getType();

    if (t1 instanceof Aloc)
      t1 = ((Aloc)t1).getType();

    if (t2 instanceof Aexp)
      t2 = ((Aexp)t2).getType();

    if (t2 instanceof Aloc)
      t2 = ((Aloc)t2).getType();

    if (!(Typing.isIntegerType(t1)))
      {
	reportTypeError(e1.info.line,e1.info.column,
			"Can't do a shift operation on "+t1);
	flag = false;
      }

    if (!(Typing.isIntegerType(t2)))
    {  
      reportTypeError(e2.info.line,e2.info.column,
		      "Shift index must be an integer "+t2);
      flag = false;
    }


    if (assign_flag)
      {
	if (e1.type instanceof Aexp)
	  {
	    if (!(((Aexp)e1.type).getType() instanceof Aloc))
	      {
		reportTypeError(e1.info.line,e1.info.column,
		    "Type of "+l.getText() + " operation must be a location "
		    +((Aexp)e1.type).getType());
	      }
	  }    
      }
	
    Line line = new Line(l.line,l.column);
    
    if (!flag)
      {
	TypeAttrib result = Typing.UnaryNumericPromotion(t1);
	return new ASTTypeAttribPair(line,new Aexp(result));
      }
    return new ASTTypeAttribPair(line,IntExp);
  }

// *************************************************************************
  public ASTTypeAttribPair typeCheckAdditiveOps (ASTTypeAttribPair e1,
						 ASTTypeAttribPair e2,
						 ModifierSet specMods,
						 LineAST l, 
						 boolean assign_flag)
  {
    boolean flag1 = true, flag2 = true;
    e1.type = getExpressionType(e1, thisEnv, specMods);
    e2.type = getExpressionType(e2, thisEnv, specMods);
    TypeAttrib result = null;
    TypeAttrib t1 = e1.type;
    TypeAttrib t2 = e2.type;

    if (t1 instanceof Aexp)
      t1 = ((Aexp)t1).getType();

    if (t1 instanceof Aloc)
      t1 = ((Aloc)t1).getType();
    
    if (t2 instanceof Aexp)
      t2 = ((Aexp)t2).getType();

    if (t2 instanceof Aloc)
      t2 = ((Aloc)t2).getType();
    
    if ((l.getText().equals("+")||(l.getText().equals("+="))))
      {
	if (t1 instanceof Aclass)
	  {
	    if (((Aclass)t1).getName().equals("java.lang.String"))
	      {
		result = t1;
	      }
	  }
	if (t2 instanceof Aclass)
	  {
	    if (((Aclass)t2).getName().equals("java.lang.String"))
	    {
	        result = t2;
	    }
	  }
      }

    if (result == null)
      {
	if (!(Typing.isNumericType(t1)))
	  {
	    reportTypeError(e1.info.line,e1.info.column,
			    "Can't perform "+l.getText()+" operation on "+t1);
	    flag1 = false;
	  }
	
	if (!(Typing.isNumericType(t2))) {
              if (e2.info == null) {
                  e2.info = e1.info;
              }
              reportTypeError(e2.info.line,e2.info.column,
                              "Can't perform "
                              + l.getText()
                              + " operation on " + t2);
              flag2 = false;
        }
      }
    
    if (assign_flag)
      {
	if (e1.type instanceof Aexp)
	  {
	    if (!(((Aexp)e1.type).getType() instanceof Aloc))
	      {
		reportTypeError(e1.info.line,e1.info.column,
		    "Type of "+l.getText()+ " operation must be a location "
		    +((Aexp)e1.type).getType());
	      }
	  }    
      }
    
    Line line = new Line(l.line,l.column);
    if ((flag1)&&(flag2))
    {
      if (result == null)
	{
	  result = Typing.BinaryNumericPromotion(t1,t2);
	}
      return new ASTTypeAttribPair(line,new Aexp(result));
    }

    return new ASTTypeAttribPair(line,IntExp);
  }

// *************************************************************************
  public ASTTypeAttribPair typeCheckRelOps (ASTTypeAttribPair e1,
					    ASTTypeAttribPair e2, 
					    ModifierSet specMods,
					    LineAST l)
  {
    e1.type = getExpressionType(e1, thisEnv, specMods);
    e2.type = getExpressionType(e2, thisEnv, specMods);
    TypeAttrib t1 = e1.type;
    TypeAttrib t2 = e2.type;

    if (t1 instanceof Aexp)
      t1 = ((Aexp)t1).getType();

    if (t1 instanceof Aloc)
      t1 = ((Aloc)t1).getType();

    if (t2 instanceof Aexp)
      t2 = ((Aexp)t2).getType();

    if (t2 instanceof Aloc)
      t2 = ((Aloc)t2).getType();
    
    if (!(Typing.isNumericType(t1)))
      {
	reportTypeError(e1.info.line,e1.info.column,
		"Can't perform "+l.getText()+ " operation on "+t1);
      }
    
    if (!(Typing.isNumericType(t2)))
      {
	reportTypeError(e2.info.line,e2.info.column,
		"Can't perform "+l.getText()+" operation on "+t2);
      }

    Line t = new Line(l.line,l.column);
    
    return new ASTTypeAttribPair(t, boolExp);
  }

// *************************************************************************
  public ASTTypeAttribPair typeCheckBoolExps (ASTTypeAttribPair e1, 
					      ASTTypeAttribPair e2, 
					      ModifierSet specMods,
					      LineAST l)
    {
        e1.type = getExpressionType(e1, thisEnv, specMods);
        e2.type = getExpressionType(e2, thisEnv, specMods);
        if (e1.type instanceof Aexp)
            e1.type = ((Aexp)e1.type).getType();
        
        if (e1.type instanceof Aloc)
            e1.type = ((Aloc)e1.type).getType();
        
        if (e2.type instanceof Aexp)
            e2.type = ((Aexp)e2.type).getType();
        
        if (e2.type instanceof Aloc)
            e2.type = ((Aloc)e2.type).getType();
        
        if (!(e1.type.equals(new Builtin("boolean"))))
            {
                reportTypeError(e1.info.line,e1.info.column,
				"Expected a boolean expression, found "
                                + e1.type);
            }
        if (!(e2.type.equals(new Builtin("boolean"))))
            {
                reportTypeError(e2.info.line,e2.info.column,
				"Expected a boolean expression, found "
                                + e2.type);
            }
        Line t = new Line(l.line,l.column);
        return new ASTTypeAttribPair(t, boolExp);
    }
    
    // *************************************************************************
    public void typeCheckRefines(LineAST id,String packageName) 
    {
        File f1;
        if (packageName.equals("")) {
            f1 = new File (".");
        } else {
            Search s = new Search(packageName, true);
            f1 = s.result();
        }
        if (f1 != null) {
            String name = id.getText().substring(1,id.getText().length()-1);
            String cname = name.substring(0,name.lastIndexOf('.'));
            String filename = f1.getPath()+File.separator+name;
            
            File f = new File(filename);
            if (f.exists()) {
		String fqn = packageName+"."+cname; 
                
                try {
                    Adec tdec = JmlChecking.runTypeChecker(f);
                    if (tdec == null) {
                        errors ++;
                    }
                } catch (java.io.IOException e) {
                    errors++;
                    reportTypeError(id.line, id.column,
                                    "cannot read " + e.getMessage());
                }
                return ;
                
            }
        }
        // otherwise the file wasn't found, so need to count an error for that
        errors ++;
    }
    
    // *************************************************************************
    public static void reportError (String filename, int line, int column, 
                                    String mesg)
    {
        System.err.println(filename+":"+line+":(Col "+column+"): "+mesg);
    }
    
    // *************************************************************************
    public void reportTypeError (int line, int column, String mesg)
    {	
        errors++;
        reportError(inputFile,line,column,mesg);
    }
    
    // *************************************************************************
    public void reportTypeError (Aerr err)
    {	
        errors++;
        reportError(inputFile, err.line, err.column, err.message);
	}
    LB */
}


