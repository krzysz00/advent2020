#!/usr/bin/env perl
use 5.024;
use strict;
use warnings;

print <<'PROLOGUE';
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinInt.
Open Scope Z_scope.

Add LoadPath ".".
Require Import advent12.

Definition input : list cmd :=
PROLOGUE

while (<>) {
    print ($. == 1 ? "[ " :  "; ");
    s/^(.)/$1 /;
    print;
}
print "].\n";
print <<'EPILOGUE';

Compute part_a input.
Compute part_b input.
EPILOGUE
