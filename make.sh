#!/bin/sh

. vars.sh

export PATH=$CLANGDIR:$PATH

INCLUDEOPTS=-I,$VELLVMDIR/Extraction/_build,-I,$LLVMDIR/lib/ocaml,-I,$CSEMDIR/_ocaml_generated/_build
CCOPTS=-cc,clang++
LIBOPTS=-cclib,-lLLVMAnalysis,-cclib,-lLLVMTarget,-cclib,-lllvm_analysis,-cclib,-lllvm_target

BASEMODS="-mod either -mod nat_num -lib nums -mod pset -mod pmap -lib str"
LEMMODS="-mod lem -mod lem_basic_classes -mod lem_bool -mod lem_tuple -mod lem_maybe -mod lem_either -mod lem_function -mod lem_num -mod lem_map -mod lem_set -mod lem_list -mod lem_string -mod lem_word -mod lem_pervasives -mod lem_relation"
CSEMMODS="-pkg pprint -lib PPrintLib -lib unix -mod input -mod implementation_ -mod colour -mod symbol -mod cmm_aux -mod cmm_csem -mod pp_cabs0 -mod pp_symbol -mod pp_ail -mod undefined -mod pp_core -mod boot_ocaml -mod core_parser -mod pervasives_ -mod position -mod core_parser_util -mod core_lexer -mod lexer_util -mod exception -mod location -mod parser_util -mod pp_errors -mod pre_parser_aux  -mod parser_errors -mod pre_parser -mod common -mod errorMonad -mod context -mod ailTypes -mod ailSyntax -mod builtins -mod lexer -mod parser -mod cparser_driver -mod decode_ocaml -mod product -mod global -mod multiset -mod cabs0 -mod state_exception -mod scope_table -mod cabs_to_ail_effect -mod cabs_to_ail -mod annotation -mod range -mod implementation -mod ailTypesAux -mod genTypes -mod ailWf -mod ailTyping -mod genTypesAux -mod ailSyntaxAux -mod xstring -mod genTyping -mod translation_effect -mod core -mod core_aux -mod state -mod core_ctype -mod translation_aux -mod translation -mod core_run_effect -mod core_run"

ocamlbuild -I src -cflags $INCLUDEOPTS,$CCOPTS -lflags $INCLUDEOPTS,$CCOPTS,$LIBOPTS -lib llvm -lib llvm_bitreader -lib jchl $BASEMODS $LEMMODS $CSEMMODS main.d.byte

./mkstdlib.sh /tmp/stdlib.v
diff -q -N /tmp/stdlib.v coq/stdlib.v || cp /tmp/stdlib.v coq/stdlib.v

coq_makefile -arg "-require coqharness" -arg "-impredicative-set" $COQINCLUDEOPTS -install none coq/*.v -o Makefile.coq
make -f Makefile.coq

clang -o mklimits mklimits.c && ./mklimits > limits.py
clang -o mksizeof mksizeof.c && ./mksizeof > sizeof.py
