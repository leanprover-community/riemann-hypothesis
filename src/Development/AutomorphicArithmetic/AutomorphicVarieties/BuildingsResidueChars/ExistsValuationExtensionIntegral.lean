module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralExtensionAlgClosed
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

private theorem UpperTheory.exists_ringHom_extension_of_integral (R S K : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Field K] [IsAlgClosed K]
    (hinj : Function.Injective (algebraMap R S)) (b : R →+* K) :
    ∃ Φ : S →+* K, Φ.comp (algebraMap R S) = b :=
  _root_.UpperTheory.Reformulated.B.IntegralExtensionAlgClosed.exists_ringHom_extension_of_integral R S K hinj b

theorem UpperTheory.exists_valuation_extension_integral :
    ∀ (R S K : Type) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] [Field K] [IsAlgClosed K] (V : ValuationSubring K), Function.Injective (algebraMap R S) → ∀ b : R →+* V, ∃ Φ : S →+* V, Φ.comp (algebraMap R S) = b := by
  intro R S K _ _ _ _ _ _ V hinj b
  obtain ⟨Φ, hΦ⟩ := UpperTheory.exists_ringHom_extension_of_integral R S K hinj ((algebraMap V K).comp b)
  have hmem : ∀ s : S, Φ s ∈ V := by
    intro s
    have hs : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    have h2 : IsIntegral V (Φ s) := hs.map_of_comp_eq b Φ hΦ.symm
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := K)).1 h2
    rw [← hy]; exact y.2
  refine ⟨Φ.codRestrict V hmem, ?_⟩
  ext r
  exact RingHom.congr_fun hΦ r
