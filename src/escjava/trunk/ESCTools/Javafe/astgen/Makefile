# Copyright 2000, 2001, Compaq Computer Corporation

LEX =		flex
CFLAGS = 	-g

all: astgen astfilelist

astgen: lex.yy.o astutil.o astactions.o astoutput.o
	cc -o astgen lex.yy.o astutil.o astactions.o astoutput.o

astfilelist: lex.yy.o astutil.o astfilelistactions.o
	cc -o astfilelist lex.yy.o astutil.o astfilelistactions.o

lex.yy.c: astgen.l
	flex astgen.l

lex.yy.o: lex.yy.c astactions.h

astutil.o: astutil.h astutil.c

astactions.o: astutil.h astactions.h astoutput.h astactions.c

astfilelistactions.o: astutil.h astactions.h astoutput.h astfilelistactions.c

astoutput.o: astutil.h astoutput.h astoutput.c

clean: tidy
	rm -f astgen astfilelist

tidy:
	rm -f lex.yy.* *.o *~
