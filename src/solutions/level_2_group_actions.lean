import group_theory.group_action.basic
import tactic
import data.setoid.partition

variables {G : Type*} [group G] {S : Type} {s t u : S} [mul_action G S]

open mul_action

theorem mem_orbit_refl (s : S) : s ∈ orbit G s :=
begin
  -- we could use `1 : G` but this is already in the library under another name
  exact mem_orbit_self s,
end

theorem mem_orbit_symm (h : s ∈ orbit G t) : t ∈ orbit G s :=
begin
  rw mem_orbit_iff at *,
  -- h says ∃ x, x • t = s so let's let `a` be that `x` and 
  -- then replace `s` by `a • t` everywhere (that's the `rfl`)
  rcases h with ⟨a, rfl⟩,
  -- By the maths proof, we use a⁻¹
  use a⁻¹,
  -- now the simplifier can solve this equality
  simp,
end

theorem mem_orbit_trans (hst : s ∈ orbit G t) (htu : t ∈ orbit G u) :
  s ∈ orbit G u :=
begin
  rw mem_orbit_iff at *,
  -- we know a • t = s and b • u = t
  rcases hst with ⟨a, rfl⟩,
  rcases htu with ⟨b, rfl⟩,
  -- so we have to solve `∃ x, x • u = a • b • u` 
  use a * b,
  exact mul_smul a b u, -- I know the axiom name
end

open set

variable (G)

theorem orbit_nonempty (s : S) : set.nonempty (orbit G s) :=
begin
  rw nonempty_def,
  -- the orbit is nonempty because it contains s
  use s,
  -- and here's the proof that s is in its own orbit
  exact mem_orbit_refl s,
end

variable {G}
theorem mem_orbit (s : S) : ∃ (t : S), s ∈ orbit G t :=
begin
  -- we can use t = s
  use s,
  -- and here's the proof that s is in its own orbit
  exact mem_orbit_refl s,
end

variable {a : S}

theorem boring_lemma (has : a ∈ orbit G s) (hat : a ∈ orbit G t) : s ∈ orbit G t :=
begin
  -- this is a little logic puzzle. Note that my proof is backwards
  refine mem_orbit_trans _ hat,
  exact mem_orbit_symm has,
end

theorem orbit_subset_of_mem_orbit (hst : s ∈ orbit G t) : orbit G s ⊆ orbit G t :=
begin
  rintros u hu,
  exact mem_orbit_trans hu hst,
end

theorem orbit_eq_orbit_of_mem_inter (has : a ∈ orbit G s) (hat : a ∈ orbit G t) :
  orbit G s = orbit G t :=
begin
  -- ⊆ is antisymmetric
  apply subset.antisymm,
  { -- both cases follow from the boring lemma and `orbit_subset_of_mem_orbit`
    apply orbit_subset_of_mem_orbit,
    exact boring_lemma has hat, },
  { apply orbit_subset_of_mem_orbit,
    exact boring_lemma hat has, }
end

variable {g : G}

open setoid

-- this is harder and can probably be golfed.
example : is_partition {𝒪 : set S | ∃ s, orbit G s = 𝒪} :=
begin
  refine ⟨_, _⟩,
  { rintro ⟨s, hs⟩,
    exact not_nonempty_iff_eq_empty.mpr hs (orbit_nonempty G s), },
  intro s,
  refine exists_unique_of_exists_of_unique _ _,
  { use orbit G s,
    simp },
  { rintro A B ⟨⟨t, rfl⟩, hst, -⟩ ⟨⟨u, rfl⟩, hsu, -⟩,
    exact orbit_eq_orbit_of_mem_inter hst hsu, },
end
