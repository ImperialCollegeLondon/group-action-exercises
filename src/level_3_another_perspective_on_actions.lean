/- 
Apache 2, because everyone else is doing it
Written by Kevin Buzzard summer 2021 in his shed.
Powered by `mathlib`, the leanprover-community, without which nothing
would have happened.
Thanks to Leo and everyone at Microsoft Research for Lean.
-/
-- This imports all user tactics and a whole bunch of basic mathematics
import tactic
import group_theory.group_action.basic -- group actions
import data.setoid.partition
/-!

# Level 3 : actions are certain group homomorphisms

A mathematician might say: "to give a left action of G on S is to
give a group homomorphism `G → Aut(S)`". This sentence is problematic
but can be fixed.

## Introduction : saying what we mean by "to give X is to give Y"

Two types `X` and `Y` can "represent the same data". For example
if `S` is a type then the type of equivalence relations on `S` and
the type of partitions of `S`  are two ways of formalising the same
mathematical idea. 

We formalise the idea that `X` and `Y` are somehow "the same"




This sentence is problematic,
because whilst it claims that there is some "canonical" construction
between two things, it leaves implicit the actual construction. Global class
field theory teaches us that sometimes there is more than one "canonical" 
way to normalise bijections. Lean would prefer, in simple cases like this,
that we spell the bijection out.

-/


/-

## Introduction

We know what a mathematician means when they say "let G be a group"
  or "let S be a set/type". But what do they mean when they say "Assume
  G acts on S", or "assume S is a G-set"? 

Here is a precise answer.

## Section 2.1 : Definition of group actions