/* Copyright 2000, 2001, Compaq Computer Corporation */

#include <stdio.h>
#include <ctype.h>
#include <assert.h>
#include "astutil.h"
#include "astoutput.h"

void outputStartOfFile(FILE *o, const char *text, int len)
{ fwrite(text, len, 1, o); }

void outputExpansion(FILE *o, Class *c, DirectiveListNode *d)
{
  int nonnull;
  switch(d->tag) {
  case FIELDDIRECTIVE:
    nonnull = d->i.f.notnull && !isJavaPrimitiveType(d->i.f.type);
    if (d->i.f.notnullloc) {
      indent(o, d->indent);
      fprintf(o, "//@ invariant %s != javafe.util.Location.NULL;\n", d->i.f.name);
    }
    if (d->i.f.syntax) {
      indent(o, d->indent);
      fprintf(o, "//@ invariant %s.syntax;\n", d->i.f.name);
    }
    indent(o, d->indent);
    fprintf(o, "public %s%s%s %s;\n\n",
	    (nonnull ? "/*@ non_null */ " : ""),
	    d->i.f.type,
	    (d->i.f.sequence ? VECTORSUFFIX : ""),
	    d->i.f.name);
    break;
  case NOMAKERDIRECTIVE:
  case MANUALTAGDIRECTIVE:
  case POSTMAKECALLDIRECTIVE:
  case POSTCHECKCALLDIRECTIVE:
  case MAKERSPECDIRECTIVE:
    break;
  default: assert(0);
  }
}


static boolean isJavaPrimitiveType(const char *s)
{
   if (strcmp(s, "boolean") == 0) return TRUE;
   if (strcmp(s, "byte") == 0) return TRUE;
   if (strcmp(s, "short") == 0) return TRUE;
   if (strcmp(s, "int") == 0) return TRUE;
   if (strcmp(s, "long") == 0) return TRUE;
   if (strcmp(s, "char") == 0) return TRUE;
   if (strcmp(s, "float") == 0) return TRUE;
   if (strcmp(s, "double") == 0) return TRUE;
   return FALSE;
}

#define FOREACHDIRECTIVE(D,SET) \
  for((D) = (SET); (D); (D) = (D)->next)

#define FOREACHLOCALFIELD(D,SET) \
  FOREACHDIRECTIVE(D,SET) \
     if ((D)->tag == FIELDDIRECTIVE)

#define FOREACHFIELD(C,D,CLASSLIST) \
  for((C) = (CLASSLIST); (C); (C) = (C)->next) \
    FOREACHLOCALFIELD(D, (C)->c->directives) \

void outputEndClass(FILE *o, Class *class, const char *text, int len,
		    const char *visitorRoot)
{
  int i, j, ind;
  boolean nomaker = FALSE, manualtag = FALSE;
  boolean postmakecall = FALSE, postcheckcall = FALSE;
  
  ClassListNode *classlist = superclassList(class);
  ClassListNode *c;
  DirectiveListNode *d;

  FOREACHDIRECTIVE(d,class->directives) {
    if (d->tag == NOMAKERDIRECTIVE) nomaker = TRUE;
    else if (d->tag == MANUALTAGDIRECTIVE) manualtag = TRUE;
    else if (d->tag == POSTMAKECALLDIRECTIVE) postmakecall = TRUE;
    else if (d->tag == POSTCHECKCALLDIRECTIVE) postcheckcall = TRUE;
  }
  ind = (class->directives ? class->directives->indent : 3);


  /*
   * Output protected constructor
   */

/* We always output the constructor here so we have a place to put the needed
   annotation. */
/*  if (! class->abstract) { */
    fprintf(o, "\n\n// Generated boilerplate constructors:\n\n");

    indent(o, ind);
    fprintf(o, "/**\n");
    indent(o, ind);

    fprintf(o, " * Construct a raw %s whose class invariant(s) have not\n",
	    class->name);
    indent(o, ind);
    fprintf(o, " * yet been established.  It is the caller's job to\n");
    indent(o, ind);
    fprintf(o, " * initialize the returned node's fields so that any\n");
    indent(o, ind);
    fprintf(o, " * class invariants hold.\n");
    indent(o, ind);
    fprintf(o, " */\n");
    indent(o, ind);
    fprintf(o, "//@ requires I_will_establish_invariants_afterwards;\n");
    indent(o, ind);
    fprintf(o, "protected %s() {}    //@ nowarn Invariant,NonNullInit\n\n", class->name);
/*  } */


  /* For root, abstract classes, output signatures of boilerplate methods. */
  if (class->abstract && class->superclass == NULL) {
    indent(o, ind);
    fprintf(o, "\n\n// Generated boilerplate methods:\n\n");

    indent(o, ind);
    fprintf(o, "/** Return the number of children a node has. */\n");
    indent(o, ind);
    fprintf(o, "//@ ensures \\result >= 0;\n");
    indent(o, ind); fprintf(o, "public abstract int childCount();\n\n");

    indent(o, ind);
    fprintf(o, "/** Return the first-but-ith child of a node. */\n");
    indent(o, ind);
    fprintf(o, "//@ requires 0 <= i;\n");
    indent(o, ind);fprintf(o, "public abstract Object childAt(int i);\n\n");

    indent(o, ind);
    fprintf(o, "/** Return the tag of a node. */\n");
    indent(o, ind); fprintf(o, "public abstract int getTag();\n\n");

    indent(o, ind);
    fprintf(o, "/** Return a string representation of <code>this</code>.\n");
    indent(o, ind);
    fprintf(o, "Meant for debugging use only, not for presentation. */\n");
    indent(o, ind); fprintf(o, "public abstract String toString();\n\n");

    indent(o, ind);
    fprintf(o,"/** Accept a visit from <code>v</code>.  This method simply\n");
    indent(o, ind);
    fprintf(o,"calls the method of <code>v</code> corresponding to the\n");
    indent(o, ind);
    fprintf(o,"allocated type of <code>this</code>, passing <code>this</code>\n");
    indent(o, ind);
    fprintf(o,"as the argument.  See the design patterns book. */\n");
    indent(o, ind);
    fprintf(o,"//@ requires v != null;\n");
    indent(o, ind);
    if (visitorRoot) {
      /* assume arg result visitor has similar root */
      char visitorArgResultRoot[1024];
      strcpy(visitorArgResultRoot, visitorRoot);
      strcat(visitorArgResultRoot, "ArgResult");
      fprintf(o, "public abstract void accept(%s v);\n\n", visitorRoot);
      indent(o, ind);
      fprintf(o,"//@ requires v != null;\n");
      fprintf(o,"//@ ensures \\result != null;\n");
      fprintf(o, "public abstract Object accept(%s v, Object o);\n\n", visitorArgResultRoot);
    }
    else {
      fprintf(o, "public abstract void accept(" VISITORCLASS " v);\n\n");
      indent(o, ind);
      fprintf(o,"//@ requires v != null;\n");
      fprintf(o,"//@ ensures \\result != null;\n");
      fprintf(o, "public abstract Object accept(" VISITORARGRESULTCLASS " v, Object o);\n\n");
    }
  }


  if (! class->abstract)
    fprintf(o, "\n// Generated boilerplate methods:\n\n");

  if (! class->abstract) {

    /* Output childCount */

    boolean doneSzDecl = FALSE;
    int simpleChildCount = 0;
    indent(o, ind); fprintf(o, "public final int childCount() {\n");
    FOREACHFIELD(c,d,classlist) {
      if (! isJavaPrimitiveType(d->i.f.type)) {
	if (d->i.f.sequence) { /* Sequence field */
	  if (! doneSzDecl) {
	    indent(o, ind+3); fprintf(o, "int sz = 0;\n");
	    doneSzDecl = TRUE;
	  }
	  indent(o, ind+3);
	  fprintf(o, "if (this.%s != null) sz += this.%s.size();\n",
		  d->i.f.name, d->i.f.name);
	} else simpleChildCount++;
      }
    }
    indent(o, ind+3);
    fprintf(o, (doneSzDecl ? "return sz + %d;\n" : "return %d;\n"),
	    simpleChildCount);
    indent(o, ind); fprintf(o, "}\n\n");

    /* Output childAt */
    indent(o, ind);
    fprintf(o, "public final Object childAt(int index) {\n");
    indent(o, ind+8); fprintf(o, "/*throws IndexOutOfBoundsException*/\n");

    indent(o, ind+3); fprintf(o, "if (index < 0)\n");
    indent(o, ind+6);
    fprintf(o, "throw new IndexOutOfBoundsException(\"AST child index \" + index);\n");
    indent(o, ind+3); fprintf(o, "int indexPre = index;\n\n");
    indent(o, ind+3); fprintf(o, "int sz;\n\n");
    FOREACHFIELD(c,d,classlist) {
      if (! isJavaPrimitiveType(d->i.f.type)) {
	char *n = d->i.f.name;
	if (d->i.f.sequence) { /* Sequence field */
	  indent(o, ind+3);
	  fprintf(o, "sz = (this.%s == null ? 0 : this.%s.size());\n", n, n);
	  indent(o, ind+3); fprintf(o, "if (0 <= index && index < sz)\n");
	  indent(o, ind+6); fprintf(o, "return this.%s.elementAt(index);\n",n);
	  indent(o, ind+3); fprintf(o, "else index -= sz;\n\n");
	} else { /* Simple field */
	  indent(o, ind+3); fprintf(o, "if (index == 0) return this.%s;\n", n);
	  indent(o, ind+3); fprintf(o, "else index--;\n\n");
	}
      }
    }
    indent(o, ind+3);
    fprintf(o, "throw new IndexOutOfBoundsException(\"AST child index \" + indexPre);\n");
    indent(o, ind); fprintf(o, "}   //@ nowarn Exception\n\n");

    /* Output toString */
    indent(o, ind); fprintf(o, "public final String toString() {\n");
    indent(o, ind+3); fprintf(o, "return \"[%s\"\n", class->name);
    FOREACHFIELD(c,d,classlist) {
      char *n = d->i.f.name;
      indent(o, ind+6);
      fprintf(o, "+ \" %s = \" + this.%s\n", n, n);
    }
    indent(o, ind+6); fprintf(o, "+ \"]\";\n");
    indent(o, ind); fprintf(o, "}\n\n");
  }


  /* Output getTag method */
  if (! class->abstract && ! manualtag) {
    int i, nlen = strlen(class->name);
    char *name2 = mktmpstr(class->name, nlen+1);

    for(i = 0; i < nlen; i++) name2[i] = toupper(name2[i]);
    
    indent(o, ind);    fprintf(o,"public final int getTag() {\n");
    indent(o, ind+3);  fprintf(o,"return TagConstants.%s;\n",name2);
    indent(o, ind);    fprintf(o,"}\n\n");
  }


  /* Output acceptor */
  if (! class->abstract) {
    indent(o, ind);
    if (visitorRoot) {
      fprintf(o, "public final void accept(%s v) { \n", visitorRoot);
      indent(o, 2*ind);
      fprintf(o, "if (v instanceof " VISITORCLASS ") ");
      fprintf(o, "((" VISITORCLASS ")v).visit%s(this);\n",
	      class->name);
      indent(o, ind);
      fprintf(o, "}\n\n");
    } else
      fprintf(o,"public final void accept(" VISITORCLASS " v) { v.visit%s(this); }\n\n",
	      class->name);

    /* output visitor arg result */
    indent(o, ind);
    if (visitorRoot) {
      /* assume arg result visitor has similar root */
      char visitorArgResultRoot[1024];
      strcpy(visitorArgResultRoot, visitorRoot);
      strcat(visitorArgResultRoot, "ArgResult");
      fprintf(o, "public final Object accept(%s v, Object o) { \n", visitorArgResultRoot);
      indent(o, 2*ind);
      fprintf(o, "if (v instanceof " VISITORARGRESULTCLASS ") ");
      fprintf(o, "return ((" VISITORARGRESULTCLASS ")v).visit%s(this, o); else return null;\n",
	      class->name);
      indent(o, ind);
      fprintf(o, "}\n\n");
    } else {
      fprintf(o,"public final Object accept(" VISITORARGRESULTCLASS " v, Object o) {"
	      "return v.visit%s(this, o); }\n\n",
	      class->name);
    }
  }

  /* Output invariant checker */
  indent(o, ind); fputs("public void check() {\n", o);
  if (class->superclass != NULL)
    { indent(o, ind+3); fputs("super.check();\n", o); }
  FOREACHFIELD(c, d, classlist)
    if (! isJavaPrimitiveType(d->i.f.type)
	&& (d->i.f.notnull || d->i.f.checkfield)) {
      int ind2 = ind+3;
      indent(o, ind2);
      if (d->i.f.notnull && ! d->i.f.checkfield)
	fprintf(o, "if (this.%s == null) throw new RuntimeException();\n",
		d->i.f.name);
      else {
	if (! d->i.f.notnull) {
	  fprintf(o, "if (this.%s != null)\n", d->i.f.name);
	  ind2 += 3;
	  indent(o, ind2);
	}
	if (d->i.f.sequence) {
	  fprintf(o, "for(int i = 0; i < this.%s.size(); i++)\n", d->i.f.name);
	  indent(o, ind2+3);
	  fprintf(o, "this.%s.elementAt(i).check();\n",
		  d->i.f.name);
	} else fprintf(o, "this.%s.check();\n", d->i.f.name);
      }
    }

  if (postcheckcall)
    { indent(o, ind+3); fputs("postCheck();\n", o); }
  indent(o, ind); fputs("}\n\n", o);

  /* Output maker */
  if (! class->abstract && ! nomaker) {
    int fieldCount;
    boolean haveName;
    char rname[32];

    /* Find fresh name for result */
    strcpy(rname, "result");
    for(haveName = FALSE, j = 0; ! haveName; j++) {
      haveName = TRUE;
      fieldCount = 0;
      FOREACHFIELD(c,d,classlist) {
	fieldCount++;
	if (strcmp(rname, d->i.f.name) == 0) {
	  haveName = FALSE;
	  sprintf(rname, "r%d", j);
	  goto retry;
	}
      }
    retry: ;
    }

    /* Output annotations for make */
    FOREACHFIELD(c, d, classlist) {
      if (d->i.f.notnullloc) {
        indent(o, ind); 
        fprintf(o, "//@ requires %s != javafe.util.Location.NULL;\n",
		d->i.f.name);
      }
      if (d->i.f.syntax) {
        indent(o, ind); 
        fprintf(o, "//@ requires %s.syntax;\n",
		d->i.f.name);
      }
    }

    FOREACHDIRECTIVE(d, class->directives) {
      if (d->tag == MAKERSPECDIRECTIVE) {
        indent(o, ind);
        fprintf(o, "//@ %s", d->i.ms.pragma);
      }
    }
    indent(o, ind); 
    fprintf(o, "//@ ensures \\result != null;\n");

    indent(o, ind); 
    fprintf(o, "public static %s make(", class->name);

    /* Output declarations of formals */
    i = fieldCount;
    FOREACHFIELD(c, d, classlist) {
      fprintf(o, "%s%s%s %s",
	      ((d->i.f.notnull && !isJavaPrimitiveType(d->i.f.type))
	       ? "/*@non_null*/ " : ""),
	      d->i.f.type,
	      (d->i.f.sequence ? VECTORSUFFIX : ""),
	      d->i.f.name);
      if (--i) fputs(", ", o);
    }
    fprintf(o, ") {\n");


    /* Output body of maker*/
    indent(o, ind+3);
    fprintf(o, "//@ set I_will_establish_invariants_afterwards = true;\n");
    indent(o, ind+3);
    fprintf(o, "%s %s = new %s();\n", class->name,
	    rname, class->name);
    FOREACHFIELD(c, d, classlist) {
      indent(o, ind+3);
      fprintf(o, "%s.%s = %s;\n", rname, d->i.f.name, d->i.f.name);
    }
    if (postmakecall)
      { indent(o, ind+3); fprintf(o, "%s.postMake();\n", rname); }
    indent(o, ind+3); fprintf(o, "return %s;\n", rname);
    indent(o, ind); fputs("}\n", o);
  }

  freeClassList(classlist);

  /* Output text to close the class */
  fwrite(text, len, 1, o);
  if (text[len-1] != '\n') fputc('\n', o);
}


void outputEndOfAstFile(const char *text, int len,
			ClassListNode *classes,
			const char *tagBase,
			const char *visitorRoot)
{
  { /* Output visitor */
    FILE *visitorOutputFile = fopen(VISITORCLASS ".java", "w");
    ClassListNode *c;

    if (! visitorOutputFile) {
      perror("astgen visitor file");
      assert(0);
    }
      
    /* Print header material */
    fwrite(text, len, 1, visitorOutputFile); /* Generic header. */
    fprintf(visitorOutputFile, "public abstract class " VISITORCLASS);
    if (visitorRoot) 
      fprintf(visitorOutputFile, " extends %s", visitorRoot);
    fprintf(visitorOutputFile, " {\n");

    for(c = classes; c != NULL; c = c->next) {
      if (c->c->superclass != NULL) { 
	/* If superclass exists, gen visit method that dispatches to
	   visit method of superclass. */
	fprintf(visitorOutputFile, "  //@ requires x != null;\n");
	fprintf(visitorOutputFile, "  public void visit%s(%s x) {\n",
		c->c->name, c->c->name);
	fprintf(visitorOutputFile, "    visit%s(x);\n",
		c->c->superclass->name);
	fprintf(visitorOutputFile, "  }\n\n");
      } else /* Gen an abstract visit method */ {
	fprintf(visitorOutputFile, "  //@ requires x != null;\n");
	fprintf(visitorOutputFile, "  public abstract void visit%s(%s x);\n\n",
		c->c->name, c->c->name);
      }
    }

    fprintf(visitorOutputFile, "}\n");
    fclose(visitorOutputFile);
  }

  { /* Output visitor arg result */
    FILE *visitorOutputFile = fopen(VISITORARGRESULTCLASS ".java", "w");
    ClassListNode *c;

    if (! visitorOutputFile) {
      perror("astgen visitor arg result file");
      assert(0);
    }
      
    /* Print header material */
    fwrite(text, len, 1, visitorOutputFile); /* Generic header. */
    fprintf(visitorOutputFile, "public abstract class " VISITORARGRESULTCLASS);
    if (visitorRoot) {
      /* assume arg result visitor has similar root */
      char visitorArgResultRoot[1024];
      strcpy(visitorArgResultRoot, visitorRoot);
      strcat(visitorArgResultRoot, "ArgResult");
      fprintf(visitorOutputFile, " extends %s", visitorArgResultRoot);
    }
    fprintf(visitorOutputFile, " {\n");
    
    for(c = classes; c != NULL; c = c->next) {
      if (c->c->superclass != NULL) { 
	/* If superclass exists, gen visit method that dispatches to
	   visit method of superclass. */
	fprintf(visitorOutputFile, "  //@ requires x != null;\n");
	fprintf(visitorOutputFile, "  //@ ensures \\result != null;\n");
	fprintf(visitorOutputFile, "  public Object visit%s(%s x, Object o) {\n",
		c->c->name, c->c->name);
	fprintf(visitorOutputFile, "    return visit%s(x, o);\n",
		c->c->superclass->name);
	fprintf(visitorOutputFile, "  }\n\n");
      } else /* Gen an abstract visit method */ {
	fprintf(visitorOutputFile, "  //@ requires x != null\n");
	fprintf(visitorOutputFile, "  //@ ensures \\result != null;\n");
	fprintf(visitorOutputFile, "  public abstract Object visit%s(%s x, Object o);\n\n",
		c->c->name, c->c->name);
      }
    }

    fprintf(visitorOutputFile, "}\n");
    fclose(visitorOutputFile);
  }

  { /* Output constants */
    FILE *constOutputFile = fopen(TAGSBASECLASS ".java", "w");
    int makeClass = 1;
    ClassListNode *c;

    if (! constOutputFile) {
      perror("astgen constants file");
      assert(0);
    }
      
    /* Print header material */ 
    fwrite(text, len, 1, constOutputFile); /* Generic header. */
    if (!makeClass)
	fprintf(constOutputFile, "public interface " TAGSBASECLASS " {\n");
    else if (strcmp(tagBase,"0")==0) {
	fprintf(constOutputFile, "public class " TAGSBASECLASS " {\n");
    } else {
	/* Should generalize this - the super class name is part of
	   tagBase - but I'll wait until it is needed.
	*/
	fprintf(constOutputFile, "public class " TAGSBASECLASS " extends javafe.tc.TagConstants {\n");
    }
  
    /* Output the tags */
    {
	const char *previousTag = tagBase;
	ClassListNode *c;
	const char* prefix = "static public final ";
        if (!makeClass) prefix = "";
	for(c = classes; c != NULL; c = c->next) {
	    int manualtag = FALSE;
	    DirectiveListNode *d;
	    FOREACHDIRECTIVE(d,c->c->directives)
	      if (d->tag == MANUALTAGDIRECTIVE) manualtag = TRUE;
	    if (! manualtag && ! c->c->abstract) {
		/* get name of tag in upper case */
		int i, nlen = strlen(c->c->name);
		char *currentTag = mkstr(c->c->name, nlen+1);
		for(i = 0; i < nlen; i++)
		  currentTag[i] = toupper(currentTag[i]);

		indent(constOutputFile, 3);
		if (previousTag == tagBase)
		  fprintf(constOutputFile,"%sint %s = %s;\n",
			  prefix, currentTag, tagBase);
		else {
		    fprintf(constOutputFile, "%sint %s = %s + 1;\n",
			    prefix, currentTag, previousTag);
		    free(previousTag);
		}
		previousTag = currentTag;
	    }
	}
	indent(constOutputFile, 3);
	fprintf(constOutputFile, "%sint LAST_TAG = %s;\n",prefix,previousTag);
	if (previousTag == tagBase) free(previousTag);
    }
    if (makeClass) {
	fprintf(constOutputFile,"\n\n    static public String toString(int tag) {\n");
	fprintf(constOutputFile,"      switch (tag) {\n");
	for(c = classes; c != NULL; c = c->next) {
	    int manualtag = FALSE;
	    DirectiveListNode *d;
	    FOREACHDIRECTIVE(d,c->c->directives)
	      if (d->tag == MANUALTAGDIRECTIVE) manualtag = TRUE;
	    if (! manualtag && ! c->c->abstract) {
		/* get name of tag in upper case */
		int i, nlen = strlen(c->c->name);
		char *currentTag = mkstr(c->c->name, nlen+1);
		for(i = 0; i < nlen; i++)
		  currentTag[i] = toupper(currentTag[i]);

		indent(constOutputFile, 8);
		fprintf(constOutputFile,"case %s: return \"%s\";\n",
			  currentTag,currentTag);
		free(currentTag);
	    }
	}
	if (strcmp(tagBase,"0")==0) 
	    fprintf(constOutputFile,"        default: return \"Unknown javafe GeneratedTag \" + tag; \n      }\n    }\n");
	else
	    /* This needs generalization - when it needs it */
	    fprintf(constOutputFile,"        default: return javafe.tc.TagConstants.toString(tag); \n      }\n    }\n");

    }
    fprintf(constOutputFile, "}\n");
    fclose(constOutputFile);
  }
}

