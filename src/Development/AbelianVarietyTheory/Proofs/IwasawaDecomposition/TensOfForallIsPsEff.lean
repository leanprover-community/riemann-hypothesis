module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySubsingletonCohAmplePsEff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.tens_of_forall_isPsEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → IsAmpleLB (tens A N) := by
  intro k _ X f hf A N hA hN hpe
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  have hT : (tens A N).IsLB := isLB_tens hA.isLB hN
  refine isAmpleLB_of_subsingleton_coh_one X (tens A N) hT fun F hF => ?_
  obtain ⟨j₀, hj⟩ := eventually_subsingleton_coh_ample_psEff k X f hf A N hA hN hpe F hF
  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have h1 := hj (max j₀ 1) (max j₀ 1) (le_max_left _ _) le_rfl 1 one_pos
  have hpow (L : LB X) (hL : L.IsLB) (n : ℕ) (h : (lbPow L n).IsLB) :
      cls _ h = n • cls L hL := by
    rw [cls_linComb hL, Fintype.sum_unique, pull_id, natCast_zsmul]
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq F
    (isLB_tens (isLB_lbPow hA.isLB (max j₀ 1)) (isLB_lbPow hN (max j₀ 1)))
    (isLB_lbPow hT (max j₀ 1)) (by
      rw [cls_tens (isLB_lbPow hA.isLB _) (isLB_lbPow hN _), hpow A hA.isLB, hpow N hN,
        hpow (tens A N) hT, cls_tens hA.isLB hN, smul_add])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 1 i).symm.injective.subsingleton

end GlobalTheory
