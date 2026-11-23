module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
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
public import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

section Regrading

variable {σ R M M' : Type*} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']

theorem weight_comp_addMonoidHom (φ : M →+ M') (w : σ → M) (d : σ →₀ ℕ) :
    Finsupp.weight (fun v => φ (w v)) d = φ (Finsupp.weight w d) := by
  simp [Finsupp.weight_apply, map_finsuppSum, map_nsmul]

theorem weightedHomogeneousComponent_comp_addMonoidHom (φ : M →+ M') (hφ : Function.Injective φ)
    (w : σ → M) (b : M) (f : MvPolynomial σ R) :
    weightedHomogeneousComponent (fun v => φ (w v)) (φ b) f = weightedHomogeneousComponent w b f := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent,
    weight_comp_addMonoidHom, hφ.eq_iff]

end Regrading

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]

def lexRelabel (e : K ≃ Fin (Fintype.card K)) : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex (fun j => b (e.symm j))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lexRelabel_surjective (e : K ≃ Fin (Fintype.card K)) : Function.Surjective (lexRelabel e) :=
  fun i => ⟨fun k => ofLex i (e k), by
    change toLex (fun j => ofLex i (e (e.symm j))) = i
    simp only [Equiv.apply_symm_apply]
    rfl⟩

theorem lexRelabel_injective (e : K ≃ Fin (Fintype.card K)) : Function.Injective (lexRelabel e) := by
  intro a b h
  have h' : (fun j => a (e.symm j)) = fun j => b (e.symm j) := toLex.injective h
  funext k
  simpa using congrFun h' (e k)

variable [DecidableEq K] [DecidableEq (Lex (Fin (Fintype.card K) → ℕ))]

theorem isHomogeneous_lex_of_isMultiHomogIdeal (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v));
    I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro i r hr
  change ((weightedDecomposition R (fun v => lexRelabel e (blockWeight ι v))).decompose' r i :
    MRing ι R) ∈ I
  rw [weightedDecomposition.decompose'_apply]
  obtain ⟨b, rfl⟩ := lexRelabel_surjective e i
  rw [weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact hI r hr b

theorem isMultiHomogIdeal_of_isHomogeneous_lex (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)}
    (hI : letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v));
      I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))) :
    IsMultiHomogIdeal I := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro f hf b
  rw [← weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact weightedHomogeneousComponent_mem_of_mem R _ hI hf _

end Lex

theorem MinimalPrimeMultiHomog.proof : MinimalPrimeMultiHomog.Statement := by
  intro R _ K _ _ ι J W hJ hW
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := isHomogeneous_lex_of_isMultiHomogIdeal e hJ
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal.IsPrime := hWp.homogeneousCore
  have hJle : J ≤ (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal := by
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) hW.1.2
  have hle : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal ≤ W := Ideal.toIdeal_homogeneousCore_le (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) W
  have heq : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal = W := le_antisymm hle (hW.2 ⟨hcore, hJle⟩ hle)
  apply isMultiHomogIdeal_of_isHomogeneous_lex e
  rw [← heq]
  exact (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).isHomogeneous

end GroundTheory.Heights₂.Heights.NumbersDVR
