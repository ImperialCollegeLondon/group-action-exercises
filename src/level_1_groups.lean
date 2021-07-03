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

# Level 1 : Groups

In this level we demonstrate how a mathematician works with groups
in Lean.
-/

/-

## Introduction

When a mathematician says "Let $(G,\times)$ be a group" they mean the following.
They are postulating the existence of a `Type` (or a `Set`, it makes no
difference) called `G`, which has

* Structure
such as `1 : G`, `⁻¹ : G → G` and `* : G → G → G`
* Axioms and theorems 
such as 
`mul_assoc g h k : (g * h) * k = g * (h * k)`
`mul_one g : g * 1 = g` 
`mul_inv_rev g h : (g * h)⁻¹ = h⁻¹ * g⁻¹`

In this Lean file, I'll explain how to say "Let $G$ be a group" in Lean 3.

## Section 1 : Let $G$ be a group.

Here's how we say "let $G$ be a group with `*` as group law" in Lean.

`variables (G : Type) [group G]`

Ignorable note: the `[group G]` part means "We let Lean's square bracket system,
a.k.a. its typeclass system,  handle the fact that `G` is a group".

Here's how we say "let $g$ and $h$ be elements of $G$":

`variables (g h : G)`

Let's start by playing with these ideas. Feel free to try your
own stuff.
-/

/-

## Exercise 1 : play with #check

`#check` tells you the type of a term. The computer science colon
notation `g : G` is pronounced "`g` is a term of type `G`",
so if you put `#check g` you'll get `G`. Try it! Click on
some of the #check s below (underlined in blue) and look at the output
in the infoview. Ask yourself some questions in group theory.
Can you make them `#check`?

Tip : there should never be any *errors* in your file. Check on the
bottom left that it says 0 by the x, and that there are no red dots
on the right of that little scrollbar. If something doesn't work,
just comment it out and leave a note.

-/

-- let G be a group, and let g, h, k be elements
variables (G : Type) [group G] (g h k : G)

#check g * h -- works! Infoview reports that `g * h` is in `G`
#check (g * 1 * g * h⁻¹)^3 -- also works

#check ∀ a : G, a ^ 2 = 1 -- a Proposition

-- What can you make? Does `g / h` make sense? What do you think it means?

/-

### Technical note

Jump straight to Section 2 if you're just interested in the maths.

In Lean, actual function names aren't allowed to contain fancy maths
symbols and they always act on the left like $f(x,y)$ instead of being an
infix operator like `*` which takes its arguments on either side.
In fact `1`, `*`, `⁻¹` and even the lesser-used `/` are notation for the
following functions:

-/

example : has_mul.mul g h = g * h := begin refl end
example : has_inv.inv g = g ⁻¹ := begin refl end
example : (has_one.one : G) = 1 := begin refl end
example : has_div.div g h = g / h := begin refl end
-- what do you think g/h is equal to?

/-

## Section 2 : theorems about elements of a group

The axioms of a group in Lean look like `∀ g h k, (g * h) * k = g * (h * k)`
and `∀ g, 1 * g = g` if this is an axiom (doesn't matter if it's an axiom
or a theorem, if you think about it -- we just need access to the proof!)

If you want to use these axioms and theorems to prove stuff, the
first thing you need to learn how to do is to find out what the names
of all the theorems are. Here's two ways you can try to do it.

### `library_search`

If what you want is a (proof of a) basic and standard fact about groups
such as `1 * g = g` then you can be guaranteed that this will already be
in the library. Here's a very easy way of finding the name of this
theorem.
-/
example : g * 1 = g :=
begin
  -- click on the blue line below. Then click where it says "Try this!"
  -- and the proof will change
  library_search,
end

/-

You discover from this exercise that the theorem is called `mul_one`. Now
look at the statement of the theorem and start to learn the conventions
which we use in mathlib when naming theorems in group theory.
-/

/-

## Exercise 2 : playing with `library_search`

Remove all the sorrys below. Either use `library_search`, or, if you're
feeling lucky, `exact <name_I_guessed>`. 

Tip : I use `sorry`s so I don't get errors. Use them yourself to fill in boring
parts of proofs if you want to experiment and don't want errors everywhere.
-/

example : 1 * g = g :=
begin
  sorry
end

example : g = h * k⁻¹ ↔ g * k = h :=
begin
  sorry
end

example : g * k = h ↔ g = h * k⁻¹ :=
begin
  sorry -- compare the name of this one with the last one.
  -- technical note: that's `iff.symm` and dot notation
end

-- the library tends to not have equalities or iffs where the RHS
-- is more complicated than the left hand side.
example : g = g * 1 :=
begin
  sorry
end

-- For example, if you want the best chance of finding the fact
-- that g⁻¹⁻¹ and g are equal, then your best chance is to put
-- the more complex term on the left
example : g⁻¹⁻¹ = g :=
begin
  sorry
end

-- Try `library_search` on this one
example : g⁻¹ = h → h⁻¹ = g :=
begin
  sorry
end


-- `iff.mp` means "turn `P ↔ Q` into `P → Q`". The theorem was in the
-- library, but only in the `↔` form.

/-

## Section 3 : Prove some theorems!

Let's prove that if G is a group and if $g^2=1$ for all $g \in G$ then $G$
is abelian.

First let's write down a clear maths proof which doesn't skip anything.

Sublemma : if g^2=1 then g⁻¹ = g . Proof: easy.

Remark: In fact it's iff. Hence Another way of asking this question would
be the following: Assume `G` is a group where the inverse function is equal to
the identity function. Prove that `G` is commutative.

Proof of main result : xy=(xy)⁻¹=y⁻¹x⁻¹=yx  

Now let's do it in Lean.
-/

example : g^2 = g * g := sq g -- guess how I found that function 
-- (hint : I used tactic mode to start with)

lemma inv_eq : g * g = 1 → g⁻¹ = g :=
begin
  exact inv_eq_of_mul_eq_one, -- guess how I found that
end

-- in the middle of the proof of the big theorem below I needed a lemma 
-- so I just popped out here to find what it was called

example : (g * h) ⁻¹ = h⁻¹ * g⁻¹ := by library_search

theorem big_theorem (h : ∀ (g : G), g^2 = 1) : ∀ a b : G, a * b = b * a := 
begin
  -- let a and b be arbitrary
  intros a b,
  -- now make the sublemma
  have sublemma : ∀ g : G, g⁻¹ = g,
  { -- proof of the sublemma in squiggly brackets
    -- assume g in G
    intro g,
    -- use `inv_eq` above
    apply inv_eq,
    -- notice the square problem
    rw [← sq g],
    -- now it follows from h
    apply h,
    -- done
  },
  -- now the main proof. LHS is a * b, RHS is b * a. Let's work on LHS.
  rw ← sublemma (a * b),
  -- It's now (ab)⁻¹
  rw mul_inv_rev,
  -- it's now b⁻¹a⁻¹
  rw [sublemma a, sublemma b],
  --  it's now ba, which is the RHS,
  -- and because `rw` tries a sneaky `refl` at the end,we're done
  -- goals accomplished 🎉
end

/-

## Exercise 3 : Prove a theorem in group theory

-/

-- think of a theorem. Doesn't matter if it's easy. All you need is
-- a maths proof, `library_search` and `rw` and you can do loads of things. 