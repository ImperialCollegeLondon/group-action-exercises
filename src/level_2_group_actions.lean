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
import data.setoid.partition -- theory of partitions
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

## Section 2.1 : Definition of group actions

Let `G` be a group and let `S` be a type.

`variables (G : Type) [group G] (S : Type)`

An *action* of `G` on `S` is a function `has_scalar.smul : G → S → S`,
satisfying some axioms which we'll come to later. This function name
is rather unwieldy, but fortunately there is some notation `•` for it.
The notation and the axioms plus a bunch of theorems and constructions
all come as part of the `[mul_action G S]` typeclass.

The reason it's called an "action" is that if `g : G` then `g • _` is
a function from `S` to `S`, so it's a way of moving elements of `S` around,
or *acting* on them.

or to be super-precise a *left action* of `G` on `S`

The two axioms for `•` which make it a group action and not just a random
function are the following :

`one_smul G s : 1 • s = s`
`mul_smul g h s : (g * h) • s = g • (h • s)`

The first axiom says that `1 : G` "acts" in a completely boring way,
by not moving around anything at all. 

The second axiom says that the group action on the `S` is compatible
with `G`'s internal multiplication.

## Exercise 2.1 : prove some theorems

Prove the following theorems.
-/

-- Let G be a group, let S be a type, and say G acts on S
variables {G : Type} [group G] {S : Type} [mul_action G S]
{g h : G} {s t u : S}
-- We use squiggly brackets this time because Lean's unifier will
-- always be able to guess which group and set we're 
-- talking about

example : (g * g⁻¹) • s = s :=
begin
  sorry
end

example : g⁻¹ • g • s = s :=
begin
  sorry
end

/-

## Section 2.2 : Orbits

We can think of `•` as giving us a map `S → S` for each element of `G`.
The *orbit* of `s : S` is what we might informally write `G • s`,
namely the subset of `S` consisting of terms of the form `g • s` for `g : G`
Its full name is

`mul_action.orbit G s : set S`

but if we `open mul_action` we'll just be able to call it `orbit`.

-/

open mul_action

#check orbit G s -- set S

/-

### Orbits

Here is a brief API for orbits:

`mem_orbit_iff : t ∈ orbit G s ↔ ∃ (x : G), x • s = t`
`mem_orbit s g : g • s ∈ orbit G s`
`mem_orbit_self s : s ∈ orbit G s`

## Exercise 2.2

Why don't you try some orbit questions?

Tip 1 : I usually start with `rw mem_orbit_iff at *`
Tip 2 : work out the maths proof first, on a piece of paper.
-/

theorem mem_orbit_refl (s : S) : s ∈ orbit G s :=
begin
  sorry
end

theorem mem_orbit_symm : s ∈ orbit G t → t ∈ orbit G s :=
begin
  sorry
end

theorem mem_orbit_trans (hst : s ∈ orbit G t) (htu : t ∈ orbit G u) :
  s ∈ orbit G u :=
begin
  sorry
end

-- Did you just see a bijection between the three axioms
-- of an equivalence relation, and the three pieces of a structure in a group?

/-

## Section 2.3 : orbits are a partition

Equivalence classes form a partition of a type. Orbits do too. In other
words, an action of `G` on `S` breaks `S` up into a disjoint union
of distinct orbits for the action.

What is a partition? According to Lean, a collection `C` of subsets
of a type `S` satisfies the predicate `is_partition C` if none of the
subsets are empty, and furthermore every element of `S` is an element
of exactly one subset in `C`.

Here are the maths proofs. An orbit can't be empty, because `orbit G s`
contains `s`. Every element `s` of `S` is in an orbit because it's
in `orbit G s`. Uniqueness is harder.

I first establish a boring lemma saying that if `a ∈ orbit G s` and
`a ∈ orbit G t` then `s ∈ orbit G t`. This follows from symmetry
and transitivity of `mem_orbit` .

I next claim that if `s ∈ orbit G t` then `orbit G s ⊆ orbit G t`.
This follows from transitivity of `mem_orbit`.

Finally, if `a ∈ orbit G s` and `a ∈ orbit G t`
then I claim that `orbit G s = orbit G t`. This is because we have
inclusions in each direction, using the boring lemma.

Can you prove all this in Lean?

## Exercise 2.3 Prove that orbits form a partition.

-/

open set

variable (G)

theorem orbit_nonempty (s : S) : set.nonempty (orbit G s) :=
begin
  rw nonempty_def,
  sorry,
end

variable {G}
theorem mem_orbit (s : S) : ∃ (t : S), s ∈ orbit G t :=
begin
  sorry,
end

variable {a : S}

theorem boring_lemma (has : a ∈ orbit G s) (hat : a ∈ orbit G t) : s ∈ orbit G t :=
begin
  sorry,
end

theorem orbit_subset_of_mem_orbit (hst : s ∈ orbit G t) : orbit G s ⊆ orbit G t :=
begin
  -- you can just abuse definitional equality and start with `intro u`,
  sorry,
end

-- finally you can prove that if two orbits contain a common element
-- then they are equal

theorem orbit_eq_orbit_of_mem_inter (has : a ∈ orbit G s) (hat : a ∈ orbit G t) :
  orbit G s = orbit G t :=
begin
  sorry,
end

open setoid

-- This is very fiddly, I wouldn't worry too much about it, you've done
-- the maths part, the rest is plumbing. You'll have to look up the API
-- for `is_partition` yourself.
example : is_partition {𝒪 : set S | ∃ s, orbit G s = 𝒪} :=
begin
  sorry
end
