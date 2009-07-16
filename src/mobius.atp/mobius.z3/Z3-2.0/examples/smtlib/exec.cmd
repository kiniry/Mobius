@rem Execute examples in this directory
@set Z3=..\..\bin\z3.exe

@echo Example 1
%Z3% /m example1.smt
@echo ----------------

@echo Example 2
%Z3% /m example2.smt
@echo ----------------

@echo Example 2 (PARTIAL_MODELS=true)
%Z3% /m PARTIAL_MODELS=true example2.smt
@echo ----------------

@echo Example 3 (PARTIAL_MODELS=true)
%Z3% /m PARTIAL_MODELS=true example3.smt
@echo ----------------


@echo Example 3 
%Z3% /m example2.smt
@echo ----------------
