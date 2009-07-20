// $ANTLR 2.7.1: "doccommentlexer.g" -> "DocCommentLexer.java"$

// @(#)$Id: doccommentlexer.g,v 1.10 2001/08/02 18:36:20 leavens Exp $

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

//----------------------------------------------------------------------------
// The Documentation Comment scanner
//----------------------------------------------------------------------------

    package jml;

import java.io.InputStream;
import java.io.Reader;
import java.util.Hashtable;

import antlr.ANTLRHashString;
import antlr.ByteBuffer;
import antlr.CharBuffer;
import antlr.CharStreamException;
import antlr.CharStreamIOException;
import antlr.InputBuffer;
import antlr.LexerSharedInputState;
import antlr.NoViableAltForCharException;
import antlr.RecognitionException;
import antlr.Token;
import antlr.TokenStream;
import antlr.TokenStreamException;
import antlr.TokenStreamIOException;
import antlr.TokenStreamRecognitionException;
import antlr.collections.impl.BitSet;

public class DocCommentLexer extends antlr.CharScanner implements DocCommentLexerTokenTypes, TokenStream
 {

    // an initializer, to set the token type
    {
        setTokenObjectClass("jml.LineToken");
    }
    
    private DocLiteralsTable atsignKeywords = new DocLiteralsTable();
    
    public void tab() {
        int c = getColumn();
        int nc = c + 8 - (c % 8);
        setColumn( nc );
    }
public DocCommentLexer(InputStream in) {
	this(new ByteBuffer(in));
}
public DocCommentLexer(Reader in) {
	this(new CharBuffer(in));
}
public DocCommentLexer(InputBuffer ib) {
	this(new LexerSharedInputState(ib));
}
public DocCommentLexer(LexerSharedInputState state) {
	super(state);
	literals = new Hashtable();
	literals.put(new ANTLRHashString("abstract", this), new Integer(128));
	literals.put(new ANTLRHashString("void", this), new Integer(177));
	literals.put(new ANTLRHashString("static", this), new Integer(125));
	literals.put(new ANTLRHashString("import", this), new Integer(115));
	literals.put(new ANTLRHashString("break", this), new Integer(238));
	literals.put(new ANTLRHashString("continue", this), new Integer(239));
	literals.put(new ANTLRHashString("catch", this), new Integer(247));
	literals.put(new ANTLRHashString("for", this), new Integer(237));
	literals.put(new ANTLRHashString("else", this), new Integer(234));
	literals.put(new ANTLRHashString("byte", this), new Integer(335));
	literals.put(new ANTLRHashString("interface", this), new Integer(139));
	literals.put(new ANTLRHashString("float", this), new Integer(340));
	literals.put(new ANTLRHashString("throws", this), new Integer(146));
	literals.put(new ANTLRHashString("strictfp", this), new Integer(133));
	literals.put(new ANTLRHashString("private", this), new Integer(122));
	literals.put(new ANTLRHashString("throw", this), new Integer(241));
	literals.put(new ANTLRHashString("short", this), new Integer(337));
	literals.put(new ANTLRHashString("long", this), new Integer(339));
	literals.put(new ANTLRHashString("try", this), new Integer(245));
	literals.put(new ANTLRHashString("switch", this), new Integer(242));
	literals.put(new ANTLRHashString("this", this), new Integer(168));
	literals.put(new ANTLRHashString("null", this), new Integer(318));
	literals.put(new ANTLRHashString("public", this), new Integer(123));
	literals.put(new ANTLRHashString("extends", this), new Integer(135));
	literals.put(new ANTLRHashString("false", this), new Integer(317));
	literals.put(new ANTLRHashString("synchronized", this), new Integer(130));
	literals.put(new ANTLRHashString("case", this), new Integer(243));
	literals.put(new ANTLRHashString("final", this), new Integer(127));
	literals.put(new ANTLRHashString("true", this), new Integer(316));
	literals.put(new ANTLRHashString("transient", this), new Integer(126));
	literals.put(new ANTLRHashString("do", this), new Integer(236));
	literals.put(new ANTLRHashString("implements", this), new Integer(140));
	literals.put(new ANTLRHashString("protected", this), new Integer(124));
	literals.put(new ANTLRHashString("finally", this), new Integer(246));
	literals.put(new ANTLRHashString("char", this), new Integer(336));
	literals.put(new ANTLRHashString("if", this), new Integer(210));
	literals.put(new ANTLRHashString("const", this), new Integer(131));
	literals.put(new ANTLRHashString("return", this), new Integer(240));
	literals.put(new ANTLRHashString("instanceof", this), new Integer(304));
	literals.put(new ANTLRHashString("default", this), new Integer(244));
	literals.put(new ANTLRHashString("new", this), new Integer(170));
	literals.put(new ANTLRHashString("native", this), new Integer(129));
	literals.put(new ANTLRHashString("assert", this), new Integer(248));
	literals.put(new ANTLRHashString("int", this), new Integer(338));
	literals.put(new ANTLRHashString("class", this), new Integer(134));
	literals.put(new ANTLRHashString("while", this), new Integer(235));
	literals.put(new ANTLRHashString("boolean", this), new Integer(334));
	literals.put(new ANTLRHashString("package", this), new Integer(112));
	literals.put(new ANTLRHashString("super", this), new Integer(167));
	literals.put(new ANTLRHashString("double", this), new Integer(341));
	literals.put(new ANTLRHashString("volatile", this), new Integer(132));
caseSensitiveLiterals = true;
setCaseSensitive(true);
}

public Token nextToken() throws TokenStreamException {
	Token theRetToken=null;
tryAgain:
	for (;;) {
		Token _token = null;
		int _ttype = Token.INVALID_TYPE;
		resetText();
		try {   // for char stream error handling
			try {   // for lexical error handling
				if ((LA(1)=='@') && (_tokenSet_0.member(LA(2)))) {
					mDOC_ATSIGN_KEYWORD(true);
					theRetToken=_returnToken;
				}
				else if ((LA(1)=='\n'||LA(1)=='\r')) {
					mDOC_NL_WS(true);
					theRetToken=_returnToken;
				}
				else if ((LA(1)=='@') && (true)) {
					mDOC_ATSIGN(true);
					theRetToken=_returnToken;
				}
				else if ((_tokenSet_1.member(LA(1)))) {
					mDOC_NON_EMPTY_TEXTLINE(true);
					theRetToken=_returnToken;
				}
				else {
					if (LA(1)==EOF_CHAR) {uponEOF(); _returnToken = makeToken(Token.EOF_TYPE);}
				else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());}
				}
				
				if ( _returnToken==null ) continue tryAgain; // found SKIP token
				_ttype = _returnToken.getType();
				_returnToken.setType(_ttype);
				return _returnToken;
			}
			catch (RecognitionException e) {
				throw new TokenStreamRecognitionException(e);
			}
		}
		catch (CharStreamException cse) {
			if ( cse instanceof CharStreamIOException ) {
				throw new TokenStreamIOException(((CharStreamIOException)cse).io);
			}
			else {
				throw new TokenStreamException(cse.getMessage());
			}
		}
	}
}

	protected final void mDOC_NON_NL_WS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOC_NON_NL_WS;
		int _saveIndex;
		
		{
		switch ( LA(1)) {
		case ' ':
		{
			match(' ');
			break;
		}
		case '\t':
		{
			match('\t');
			break;
		}
		case '\u000c':
		{
			match('\f');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDOC_NL_WS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOC_NL_WS;
		int _saveIndex;
		
		{
		if ((LA(1)=='\r') && (LA(2)=='\n')) {
			match("\r\n");
		}
		else if ((LA(1)=='\r') && (true)) {
			match('\r');
		}
		else if ((LA(1)=='\n')) {
			match('\n');
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		
		}
		if ( inputState.guessing==0 ) {
			newline();
		}
		{
		_loop6:
		do {
			if ((LA(1)=='\t'||LA(1)=='\u000c'||LA(1)==' ')) {
				mDOC_NON_NL_WS(false);
			}
			else {
				break _loop6;
			}
			
		} while (true);
		}
		{
		if ((LA(1)=='*')) {
			{
			int _cnt9=0;
			_loop9:
			do {
				if ((LA(1)=='*')) {
					match('*');
				}
				else {
					if ( _cnt9>=1 ) { break _loop9; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());}
				}
				
				_cnt9++;
			} while (true);
			}
			{
			_loop11:
			do {
				if ((LA(1)=='\t'||LA(1)=='\u000c'||LA(1)==' ')) {
					mDOC_NON_NL_WS(false);
				}
				else {
					break _loop11;
				}
				
			} while (true);
			}
		}
		else {
		}
		
		}
		if ( inputState.guessing==0 ) {
			newline(); _ttype = Token.SKIP;
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mDOC_PRE_JML(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOC_PRE_JML;
		int _saveIndex;
		
		{
		if ((LA(1)=='<') && (LA(2)=='P')) {
			match("<PRE>");
		}
		else if ((LA(1)=='<') && (LA(2)=='p')) {
			match("<pre>");
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		
		}
		{
		_loop15:
		do {
			if ((LA(1)=='\t'||LA(1)=='\u000c'||LA(1)==' ')) {
				mDOC_NON_NL_WS(false);
			}
			else {
				break _loop15;
			}
			
		} while (true);
		}
		{
		if ((LA(1)=='<') && (LA(2)=='J')) {
			match("<JML>");
		}
		else if ((LA(1)=='<') && (LA(2)=='j')) {
			match("<jml>");
		}
		else if ((LA(1)=='<') && (LA(2)=='E')) {
			match("<ESC>");
		}
		else if ((LA(1)=='<') && (LA(2)=='e')) {
			match("<esc>");
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mDOC_JML_PRE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOC_JML_PRE;
		int _saveIndex;
		
		{
		if ((LA(1)=='<') && (LA(2)=='/') && (LA(3)=='J')) {
			match("</JML>");
		}
		else if ((LA(1)=='<') && (LA(2)=='/') && (LA(3)=='j')) {
			match("</jml>");
		}
		else if ((LA(1)=='<') && (LA(2)=='/') && (LA(3)=='E')) {
			match("</ESC>");
		}
		else if ((LA(1)=='<') && (LA(2)=='/') && (LA(3)=='e')) {
			match("</esc>");
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		
		}
		{
		_loop20:
		do {
			if ((LA(1)=='\t'||LA(1)=='\u000c'||LA(1)==' ')) {
				mDOC_NON_NL_WS(false);
			}
			else {
				break _loop20;
			}
			
		} while (true);
		}
		{
		if ((LA(1)=='<') && (LA(2)=='/') && (LA(3)=='P')) {
			match("</PRE>");
		}
		else if ((LA(1)=='<') && (LA(2)=='/') && (LA(3)=='p')) {
			match("</pre>");
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
		}
		
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDOC_ATSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOC_ATSIGN;
		int _saveIndex;
		
		match('@');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDOC_ATSIGN_KEYWORD(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOC_ATSIGN_KEYWORD;
		int _saveIndex;
		
		mDOC_ATSIGN(false);
		{
		int _cnt25=0;
		_loop25:
		do {
			switch ( LA(1)) {
			case 'a':  case 'b':  case 'c':  case 'd':
			case 'e':  case 'f':  case 'g':  case 'h':
			case 'i':  case 'j':  case 'k':  case 'l':
			case 'm':  case 'n':  case 'o':  case 'p':
			case 'q':  case 'r':  case 's':  case 't':
			case 'u':  case 'v':  case 'w':  case 'x':
			case 'y':  case 'z':
			{
				matchRange('a','z');
				break;
			}
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':  case 'G':  case 'H':
			case 'I':  case 'J':  case 'K':  case 'L':
			case 'M':  case 'N':  case 'O':  case 'P':
			case 'Q':  case 'R':  case 'S':  case 'T':
			case 'U':  case 'V':  case 'W':  case 'X':
			case 'Y':  case 'Z':
			{
				matchRange('A','Z');
				break;
			}
			default:
			{
				if ( _cnt25>=1 ) { break _loop25; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());}
			}
			}
			_cnt25++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			_ttype = atsignKeywords.lookup(text, DOC_UNKNOWN_KEYWORD);
			
		}
		{
		_loop27:
		do {
			if ((LA(1)=='\t'||LA(1)=='\u000c'||LA(1)==' ')) {
				mDOC_NON_NL_WS(false);
			}
			else {
				break _loop27;
			}
			
		} while (true);
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDOC_NON_EMPTY_TEXTLINE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOC_NON_EMPTY_TEXTLINE;
		int _saveIndex;
		
		boolean synPredMatched30 = false;
		if (((LA(1)=='<') && (LA(2)=='P'||LA(2)=='p') && (LA(3)=='R'||LA(3)=='r'))) {
			int _m30 = mark();
			synPredMatched30 = true;
			inputState.guessing++;
			try {
				{
				mDOC_PRE_JML(false);
				}
			}
			catch (RecognitionException pe) {
				synPredMatched30 = false;
			}
			rewind(_m30);
			inputState.guessing--;
		}
		if ( synPredMatched30 ) {
			mDOC_PRE_JML(false);
			if ( inputState.guessing==0 ) {
				_ttype =  DOC_PRE_JML;
				
			}
		}
		else {
			boolean synPredMatched32 = false;
			if (((LA(1)=='<') && (LA(2)=='/') && (_tokenSet_2.member(LA(3))))) {
				int _m32 = mark();
				synPredMatched32 = true;
				inputState.guessing++;
				try {
					{
					mDOC_JML_PRE(false);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched32 = false;
				}
				rewind(_m32);
				inputState.guessing--;
			}
			if ( synPredMatched32 ) {
				mDOC_JML_PRE(false);
				if ( inputState.guessing==0 ) {
					_ttype =  DOC_JML_PRE;
					
				}
			}
			else if ((_tokenSet_1.member(LA(1))) && (true) && (true)) {
				{
				match(_tokenSet_1);
				}
				{
				_loop36:
				do {
					if ((_tokenSet_3.member(LA(1)))) {
						{
						match(_tokenSet_3);
						}
					}
					else {
						break _loop36;
					}
					
				} while (true);
				}
			}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine());
			}
			}
			if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
				_token = makeToken(_ttype);
				_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
			}
			_returnToken = _token;
		}
		
		
		private static final long _tokenSet_0_data_[] = { 0L, 576460743847706622L, 0L, 0L, 0L };
		public static final BitSet _tokenSet_0 = new BitSet(_tokenSet_0_data_);
		private static final long _tokenSet_1_data_[] = { -9224L, -2L, -1L, -1L, 0L, 0L, 0L, 0L };
		public static final BitSet _tokenSet_1 = new BitSet(_tokenSet_1_data_);
		private static final long _tokenSet_2_data_[] = { 0L, 4535485465632L, 0L, 0L, 0L };
		public static final BitSet _tokenSet_2 = new BitSet(_tokenSet_2_data_);
		private static final long _tokenSet_3_data_[] = { -9224L, -1L, -1L, -1L, 0L, 0L, 0L, 0L };
		public static final BitSet _tokenSet_3 = new BitSet(_tokenSet_3_data_);
		
		}
