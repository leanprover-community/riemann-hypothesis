module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAA

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ExistsUniqueRelabel

section RingEquiv

variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')

theorem mem_map_iff (I : Ideal R) (x : R) : φ x ∈ I.map (φ : R →+* R') ↔ x ∈ I := by
  rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]

theorem map_mem_minimalPrimes {J W : Ideal R} (h : W ∈ J.minimalPrimes) :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes := by
  rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv]
  exact Ideal.minimalPrimes_comap_of_surjective (f := (φ.symm : R' →+* R)) φ.symm.surjective h

theorem map_mem_minimalPrimes_iff {J W : Ideal R} :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes ↔ W ∈ J.minimalPrimes := by
  refine ⟨fun h => ?_, map_mem_minimalPrimes φ⟩
  have := map_mem_minimalPrimes φ.symm h
  rwa [Ideal.map_of_equiv, Ideal.map_of_equiv] at this

theorem ringKrullDim_quot_map (V : Ideal R) :
    ringKrullDim (R' ⧸ V.map (φ : R →+* R')) = ringKrullDim (R ⧸ V) :=
  (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V _ φ rfl)).symm

theorem length_map (V W : Ideal R) [W.IsPrime] [(W.map (φ : R →+* R')).IsPrime] (hVW : V ≤ W)
    (x : R) :
    Module.length (Localization.AtPrime (W.map (φ : R →+* R')))
        (LocalizedModule (W.map (φ : R →+* R')).primeCompl
          (R' ⧸ (V.map (φ : R →+* R') ⊔ Ideal.span {φ x}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ (V ⊔ Ideal.span {x}))) := by
  set V' := V.map (φ : R →+* R')
  set W' := W.map (φ : R →+* R')
  have hVW' : V' ≤ W' := Ideal.map_mono hVW
  have : (W'.map (Ideal.Quotient.mk V')).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hVW')
  have h' := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.isLocData_atPrime_quot V' W' hVW'
  letI : Algebra R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) :=
    ((algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V')))).comp
      (φ : R →+* R')).toAlgebra
  have hal : ∀ r, algebraMap R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) r =
      algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) (φ r) := fun r => rfl
  have hS : ∀ s : R', s ∈ W'.primeCompl → φ.symm s ∈ W.primeCompl := by
    intro s hs h
    apply hs
    rw [← φ.apply_symm_apply s]
    exact (mem_map_iff φ W _).2 h
  have h : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData R
      (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) W.primeCompl V := by
    refine ⟨fun s hs => ?_, fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
    · rw [hal]
      exact h'.1 _ (fun h => hs ((mem_map_iff φ W s).1 h))
    · obtain ⟨r, s, hs, e⟩ := h'.2.1 y
      refine ⟨φ.symm r, φ.symm s, hS s hs, ?_⟩
      rw [hal, hal, φ.apply_symm_apply, φ.apply_symm_apply]
      exact e
    · rw [hal] at hr
      obtain ⟨s, hs, e⟩ := h'.2.2.1 _ hr
      refine ⟨φ.symm s, hS s hs, ?_⟩
      rw [← mem_map_iff φ V, map_mul, φ.apply_symm_apply]
      exact e
    · rw [hal]
      exact h'.2.2.2 _ ((mem_map_iff φ V v).2 hv)
  exact (h'.length_eq (φ x)).trans (h.length_eq x).symm

end RingEquiv

section MRing

variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)




include hσ












end MRing

end ExistsUniqueRelabel

universe u v w v' w'

end GroundTheory.Heights₂.Heights.Targets
