##################################################
# About this Makefile
#
# This Makefile depends on Makefile.opts
##################################################

MODULE = search

SRC = \
 clause.cpp \
 search_impl_base.cpp \
 search.cpp \
 search_fast.cpp \
 search_theorem_producer.cpp \
 search_sat.cpp \
 search_simple.cpp \
 variable.cpp \
 circuit.cpp \
 decision_engine.cpp \
 decision_engine_dfs.cpp
# decision_engine_caching.cpp \
# decision_engine_mbtf.cpp

HEADERS = search_rules.h search_theorem_producer.h decision_engine.h decision_engine_dfs.h decision_engine_caching.h decision_engine_mbtf.h

LIBRARY=libsearch.a

EXTRAFLAGS=$(DPLL_BASIC)

include ../../Makefile.local
