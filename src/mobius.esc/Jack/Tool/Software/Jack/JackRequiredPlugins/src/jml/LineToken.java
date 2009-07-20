// @(#)$Id: LineToken.java,v 1.5 2001/02/22 02:58:59 leavens Exp $

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
import antlr.*;
public class LineToken extends CommonToken 
{
    public LineToken() { super(); }
    public LineToken(int t, String txt) { super(t, txt); }
    public LineToken(int t, int c, String txt) { super(t, txt); column = c;}
  protected int column;
  public int getColumn() { return column; }
  public void setColumn(int c) { column=c; }
}
