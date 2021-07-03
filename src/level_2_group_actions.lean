/- 
Apache 2, because everyone else is doing it
Written by Kevin Buzzard summer 2021 in his shed.
Powered by `mathlib`, the leanprover-community, without which nothing
would have happened.
Thanks to Leo and everyone at Microsoft Research for Lean.
-/
-- This imports all user tactics and a whole bunch of basic mathematics
import tactic
/-!

# Level 2 : Groups acting on types

In this level we demonstrate how a mathematician works with groups
acting on types in Lean. I will assume no familiarity with the
mathematics.

In technical terms, this file is an overview of the API for `mul_action`.
-/

/-

## Introduction

We know what a mathematician means when they say "let G be a group"
  or "let S be a set/type". But what do they mean when they say "Assume
  G acts on S", or "assume S is a G-set"?

Here is a precise answer.

## Section 2.1 : Definition and basic properties of group actions

Let `G` be a group and let `S` be a type.

`variables (G : Type) [group G] (S : Type)`

An *action* of `G` on `S` is a function `has_scalar.smul : G → S → S`,
satisfying some axioms which we'll come to later. This function name
is rather unwieldy, but fortunately there is some notation `•` for it.
The notation and the axioms all come as part of the `[mul_action G S]`
typeclass.

The reason it's called an "action" is that if `g : G` then `g •` is
a function from `S` to `S`, so it's a way of moving elements of `S` around,
or *acting* on them.

The two axioms for `•` which make it a group action and not just a random
function are the following :

`one_smul G s : 1 • s = s`
`mul_smul g h s : (g * h) • s = g • (h • s)`

The first axiom says that `1 : G` "acts" in a completely boring way,
by not moving around anything at all. 

The second axiom says that the group action on the `S` is compatible
with `G`'s internal multiplication.

## Exercise 2.1

Prove the following theorems.
-/

-- Let G be a group, let S be a type, and say G acts on S
variables (G : Type) [group G] (S : Type) [mul_action G S]
(g h : G) (s t : S)

example : (g * g⁻¹) • s = s :=
begin
  sorry
end

example : g⁻¹ • g • s = s :=
begin
  sorry
end
