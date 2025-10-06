---- MODULE NyxHelpers ----
(****************************************************************************)
(* Nyx Protocol - Common Helper Operators                                  *)
(*                                                                          *)
(* This module provides common helper operators used across all Nyx        *)
(* specifications. These operators should be included via EXTENDS or       *)
(* INSTANCE statements in other modules.                                   *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers

(****************************************************************************)
(* Set Operations                                                           *)
(****************************************************************************)

\* Minimum of a set
MIN(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x <= y

\* Maximum of a set
MAX(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y

\* Minimum (lowercase alias)
Min(x, y) == IF x < y THEN x ELSE y

\* Maximum (lowercase alias)
Max(x, y) == IF x > y THEN x ELSE y

\* Absolute value
Abs(x) == IF x < 0 THEN -x ELSE x

(****************************************************************************)
(* Aggregate Functions                                                      *)
(****************************************************************************)

\* Convert set to sequence (must be defined first)
RECURSIVE SetToSeqRec(_)
SetToSeqRec(S) == 
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE y \in S : TRUE
         IN <<x>> \o SetToSeqRec(S \ {x})

SetToSeq(S) == SetToSeqRec(S)

\* Sum of set elements
RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN 0 ELSE Head(s) + SumSeq(Tail(s))

Sum(S) == IF S = {} THEN 0
          ELSE LET seq == SetToSeq(S)
               IN SumSeq(seq)

\* Average of set elements
Average(S) == IF S = {} THEN 0 ELSE Sum(S) \div Cardinality(S)

\* Aliases for compatibility
SUM(S) == Sum(S)
AVG(S) == Average(S)

\* Product of set elements
RECURSIVE ProdSeq(_)
ProdSeq(s) == IF s = <<>> THEN 1 ELSE Head(s) * ProdSeq(Tail(s))

Product(S) == IF S = {} THEN 1
              ELSE LET seq == SetToSeq(S)
                   IN ProdSeq(seq)

PRODUCT(S) == Product(S)

(****************************************************************************)
(* Sequence Helpers                                                         *)

\* Range sequence
Range(n) == [i \in 1..n |-> i]

(****************************************************************************)
(* Mathematical Functions                                                   *)
(****************************************************************************)

\* Cube root approximation
CubeRoot(x) == 
    IF x <= 0 THEN 0
    ELSE IF x = 1 THEN 1
    ELSE IF x < 8 THEN 1
    ELSE IF x < 27 THEN 2
    ELSE IF x < 64 THEN 3
    ELSE IF x < 125 THEN 4
    ELSE IF x < 216 THEN 5
    ELSE IF x < 343 THEN 6
    ELSE IF x < 512 THEN 7
    ELSE IF x < 729 THEN 8
    ELSE IF x < 1000 THEN 9
    ELSE 10

\* Square root approximation
SqrtApprox(x) ==
    IF x <= 0 THEN 0
    ELSE IF x = 1 THEN 1
    ELSE IF x < 4 THEN 1
    ELSE IF x < 9 THEN 2
    ELSE IF x < 16 THEN 3
    ELSE IF x < 25 THEN 4
    ELSE IF x < 36 THEN 5
    ELSE IF x < 49 THEN 6
    ELSE IF x < 64 THEN 7
    ELSE IF x < 81 THEN 8
    ELSE IF x < 100 THEN 9
    ELSE 10

\* Infinity representation
Infinity == 999999

\* Power function (limited to small exponents)
Power(base, exp) ==
    IF exp = 0 THEN 1
    ELSE IF exp = 1 THEN base
    ELSE IF exp = 2 THEN base * base
    ELSE IF exp = 3 THEN base * base * base
    ELSE base * base * base * base

(****************************************************************************)
(* Cryptographic and Hash Helpers                                          *)
(****************************************************************************)

\* Abstract hash function
Hash(data) == (CHOOSE h \in Nat : TRUE) % 65536

\* XOR combine operation
XOR(a, b) == (a + b) % 256

====
