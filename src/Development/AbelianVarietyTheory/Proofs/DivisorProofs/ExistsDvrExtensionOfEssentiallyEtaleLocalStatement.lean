module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionOfEssentiallyEtaleLocal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local : ∀ {K K' R S : Type} [Field K] [Field K'] [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K] [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S) [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType → φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) → ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧ (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧ (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  first | exact @GlobalTheory.exists_valuationSubring_extend_of_formallyEtale | exact GlobalTheory.exists_valuationSubring_extend_of_formallyEtale | (intros; apply GlobalTheory.exists_valuationSubring_extend_of_formallyEtale <;> assumption)
