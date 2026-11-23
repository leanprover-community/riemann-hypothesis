module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GrPolys

theorem monic_deg_equiv_card (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} = g ^ n ∧
      Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := by
  have e : {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} ≃ (Fin n → ZMod g) :=
    (monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · haveI : Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := Finite.of_equiv _ e.symm
    exact Set.toFinite _

theorem zero_part_eq (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n) :
    {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0} =
      (fun h => X * h) '' {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n - 1} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hm, hd, h0⟩
    obtain ⟨h, rfl⟩ := X_dvd_iff.mpr h0
    have hmh : h.Monic := Monic.of_mul_monic_left monic_X hm
    refine ⟨h, ⟨hmh, ?_⟩, rfl⟩
    rw [natDegree_X_mul hmh.ne_zero] at hd
    omega
  · rintro ⟨h, ⟨hm, hd⟩, rfl⟩
    refine ⟨monic_X.mul hm, ?_, ?_⟩
    · rw [natDegree_X_mul hm.ne_zero]; omega
    · simp [mul_coeff_zero]

end GlobalTheory.GrPolys

theorem GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero :
    ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} = g ^ n - g ^ (n - 1) ∧ Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} := by
  intro g _ n hn
  obtain ⟨hcS, hfS⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g n
  obtain ⟨hcT, hfT⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g (n - 1)
  set S := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n}
  set A := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0}
  set B := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0}
  have hAS : A ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hBS : B ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hfA : A.Finite := hfS.subset hAS
  have hfB : B.Finite := hfS.subset hBS
  have hU : A ∪ B = S := by
    ext f
    simp only [A, B, S, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hD : Disjoint A B := by
    rw [Set.disjoint_left]
    intro f hA hB
    exact hA.2.2 hB.2.2
  have hB : B.ncard = g ^ (n - 1) := by
    rw [show B = _ from GlobalTheory.GrPolys.zero_part_eq g n hn, Set.ncard_image_of_injective _
      (fun a b h => mul_left_cancel₀ X_ne_zero h), hcT]
  have := Set.ncard_union_eq hD hfA hfB
  rw [hU, hcS, hB] at this
  exact ⟨by omega, hfA⟩
