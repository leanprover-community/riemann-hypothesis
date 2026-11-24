module

public import Formalism.GradedWeylDivisibility.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory

namespace WeylRankEmbed

variable (R : Type) [CommRing R] {a b : ℕ} (hab : a ≤ b)

abbrev corner : Fin a × Fin a → Fin b × Fin b :=
  fun v => (Fin.castLE hab v.1, Fin.castLE hab v.2)

theorem rename_lpMinor (s : ℕ) (h1 : s ≤ a) (h2 : s ≤ b) :
    rename (corner hab) (lpMinor R s h1 h1) = lpMinor R s h2 h2 := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [corner]

theorem rename_hw (ν : Fin a → ℕ) (ν' : Fin b → ℕ)
    (h : ∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) :
    rename (corner hab) (hw R le_rfl ν) = hw R le_rfl ν' := by
  unfold hw
  rw [map_prod]
  symm
  refine (Finset.prod_of_injOn (Fin.castLE hab) ((Fin.castLE_injective hab).injOn)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_).symm
  · intro j _ hj
    have hja : ¬ (j : ℕ) < a := by
      intro hlt
      exact hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
    rw [h j, dite_eq_right hja]
    simp
  · intro i _
    rw [map_pow, rename_lpMinor R hab _ _ (by have := i.2; omega)]
    have e1 : ν' (Fin.castLE hab i) = ν i := by
      rw [h, dite_eq_left (by simp)]
      rfl
    have e2 : nuNext ν' (Fin.castLE hab i) = nuNext ν i := by
      unfold nuNext
      by_cases h1 : (i : ℕ) + 1 < a
      · rw [dite_eq_left h1, dite_eq_left (by simp; omega), h, dite_eq_left (by simpa using h1)]
        rfl
      · rw [dite_eq_right h1]
        split_ifs with h2
        · rw [h, dite_eq_right (by simpa using h1)]
        · rfl
    rw [e1, e2]
    rfl

theorem rename_rowDiv (x y : Fin a) (k : ℕ) (f : MvPolynomial (Fin a × Fin a) R) :
    rename (corner hab) (rowDiv R x y k f) =
      rowDiv R (Fin.castLE hab x) (Fin.castLE hab y) k (rename (corner hab) f) := by
  have key : (Polynomial.mapAlgHom (rename (R := R) (corner hab))).comp (rowGen R x y) =
      (rowGen R (Fin.castLE hab x) (Fin.castLE hab y)).comp (rename (corner hab)) := by
    apply MvPolynomial.algHom_ext
    intro v
    by_cases hv : v.1 = y
    · simp [rowGen, hv, corner]
    · have hv' : Fin.castLE hab v.1 ≠ Fin.castLE hab y := fun e => hv (Fin.castLE_injective hab e)
      simp [rowGen, hv, corner]
  have h2 := congrArg (fun φ => (φ f).coeff k) key
  simpa [rowDiv, Polynomial.coeff_map] using h2

theorem rename_applyWord (w : List (Fin a × Fin a × ℕ)) (f : MvPolynomial (Fin a × Fin a) R) :
    rename (corner hab) (applyWord R w f) =
      applyWord R (w.map fun x => (Fin.castLE hab x.1, Fin.castLE hab x.2.1, x.2.2))
        (rename (corner hab) f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons, List.map_cons] at ih ⊢
    rw [rename_rowDiv, ih]

end WeylRankEmbed

theorem weyl_rename_castLE_mem :
    ∀ (R : Type) [CommRing R] (a b : ℕ) (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ), (∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) → ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R a a le_rfl ν, MvPolynomial.rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f ∈ Formalism.GradedWeylDivisibility.weyl R b b le_rfl ν' := by
  intro R _ a b hab ν ν' h f hf
  change rename (WeylRankEmbed.corner hab) f ∈ _
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w.map fun x => (Fin.castLE hab x.1, Fin.castLE hab x.2.1, x.2.2), ?_⟩
    simp only
    rw [WeylRankEmbed.rename_applyWord, WeylRankEmbed.rename_hw R hab ν ν' h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory
