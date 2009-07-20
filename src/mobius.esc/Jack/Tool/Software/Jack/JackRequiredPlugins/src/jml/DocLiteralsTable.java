// @(#)$Id: DocLiteralsTable.java,v 1.6 2001/03/13 06:46:50 leavens Exp $

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

import java.util.Hashtable;
import antlr.ANTLRStringBuffer;

public class DocLiteralsTable {
    protected Hashtable jmlAtSignKeywords;

    public DocLiteralsTable() {
      jmlAtSignKeywords = new Hashtable();

      jmlAtSignKeywords.put("@author",
		  new Integer(JavaTokenTypes.DOC_AUTHOR));    
      jmlAtSignKeywords.put("@deprecated",
		  new Integer(JavaTokenTypes.DOC_DEPRECATED));
      jmlAtSignKeywords.put("@exception",
		  new Integer(JavaTokenTypes.DOC_EXCEPTION));
      jmlAtSignKeywords.put("@param", 
		  new Integer(JavaTokenTypes.DOC_PARAM)); 
      jmlAtSignKeywords.put("@return",
		  new Integer(JavaTokenTypes.DOC_RETURN));
      jmlAtSignKeywords.put("@see",
		  new Integer(JavaTokenTypes.DOC_SEE));
      jmlAtSignKeywords.put("@serial",
		  new Integer(JavaTokenTypes.DOC_SERIAL));
      jmlAtSignKeywords.put("@serialData",
		  new Integer(JavaTokenTypes.DOC_SERIALDATA));
      jmlAtSignKeywords.put("@serialField",
		  new Integer(JavaTokenTypes.DOC_SERIALFIELD));
      jmlAtSignKeywords.put("@since", 
		  new Integer(JavaTokenTypes.DOC_SINCE));       
      jmlAtSignKeywords.put("@throws",
		  new Integer(JavaTokenTypes.DOC_THROWS));
      jmlAtSignKeywords.put("@version",    
		  new Integer(JavaTokenTypes.DOC_VERSION));    
    }

  public int lookup(ANTLRStringBuffer text, int defaultType) {
    Integer tokenType = (Integer)jmlAtSignKeywords.get(text.toString());
    if (tokenType != null) {
      return(tokenType.intValue());
    }
    else {
      return(defaultType);
    }
  }
};

