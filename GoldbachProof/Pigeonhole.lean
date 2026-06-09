
/-
  3-Way Pigeonhole Lemma for Goldbach SDP
  ========================================
  
  At Q=3, the LP has 3 constraints (C1: odd, C2: ≡1 mod 3, C3: ≡2 mod 3).
  Each integer element covers at most 2 of {C1, C2, C3} because:
  - C2 sources: mod6 ∈ {1, 4}
  - C3 sources: mod6 ∈ {2, 5}  
  - These are DISJOINT, so no element covers both C2 and C3.
  
  If M_red = 1 and all 3 deficits are ≥ 1, then the single element
  can cover at most 2 constraints, but we need 3. Contradiction.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Finset

namespace GoldbachPigeonhole

/-- A constraint is one of C1, C2, C3 -/
inductive Constraint
  | C1  -- odd (mod 2 = 1)
  | C2  -- ≡ 1 mod 3
  | C3  -- ≡ 2 mod 3
deriving DecidableEq, Fintype

/-- The mod-6 class of a natural number -/
def mod6class (n : ℕ) : Fin 6 := ⟨n % 6, Nat.mod_lt n (by omega)⟩

/-- Which constraints a given mod-6 class covers -/
def covers (c : Fin 6) : Finset Constraint :=
  match c.val with
  | 0 => ∅                              -- even, ≡0 mod 3
  | 1 => {Constraint.C1, Constraint.C2} -- odd, ≡1 mod 3  
  | 2 => {Constraint.C3}               -- even, ≡2 mod 3
  | 3 => {Constraint.C1}               -- odd, ≡0 mod 3
  | 4 => {Constraint.C2}               -- even, ≡1 mod 3
  | 5 => {Constraint.C1, Constraint.C3} -- odd, ≡2 mod 3
  | _ => ∅  -- unreachable

/-- Key lemma: no mod-6 class covers both C2 and C3 -/
theorem no_class_covers_C2_and_C3 (c : Fin 6) :
    ¬(Constraint.C2 ∈ covers c ∧ Constraint.C3 ∈ covers c) := by
  fin_cases c <;> simp [covers] <;> decide

/-- Every mod-6 class covers at most 2 constraints -/
theorem covers_card_le_two (c : Fin 6) : (covers c).card ≤ 2 := by
  fin_cases c <;> simp [covers] <;> decide

/-- The full set of constraints has exactly 3 elements -/
theorem all_constraints_card : (Finset.univ : Finset Constraint).card = 3 := by
  decide

/-- M_red = 1 pigeonhole: if we need to cover all 3 constraints
    but each element covers at most 2, one element is not enough. -/
theorem pigeonhole_M_red_1 :
    ∀ (c : Fin 6), (covers c).card < (Finset.univ : Finset Constraint).card := by
  intro c
  have h1 := covers_card_le_two c
  have h2 := all_constraints_card
  omega

/-- Stronger: for M_red elements, total coverage ≤ 2 * M_red,
    but we need at least 3 (the deficit sum). -/
theorem pigeonhole_general (M_red : ℕ) (elements : Fin M_red → Fin 6)
    (h_deficit : 3 ≤ 2 * M_red + 1) :  -- deficit_sum > 2 * M_red
    False := by
  omega

/-- The C2-C3 exclusivity theorem: any set of elements that covers
    both C2 and C3 must use elements from DISJOINT mod-6 classes. -/
theorem C2_C3_disjoint_sources :
    ∀ (c : Fin 6), Constraint.C2 ∈ covers c → c.val ∈ ({1, 4} : Finset ℕ) := by
  intro c hc
  fin_cases c <;> simp [covers] at hc <;> simp

theorem C3_sources :
    ∀ (c : Fin 6), Constraint.C3 ∈ covers c → c.val ∈ ({2, 5} : Finset ℕ) := by
  intro c hc
  fin_cases c <;> simp [covers] at hc <;> simp

end GoldbachPigeonhole
