module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsNef.isPsEff_pull_red_of_dim_le (k : Type) [Field k] [Infinite k] (d : ℕ)
    (H : ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) →
      topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N →
        IsAmpleLB (CechPic.tens A N))
    (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k (X := X))) (M : LB X)
    (hM : IsNef k M) (Z : Closeds X) (hZ : IsIrreducible (Z : Set X))
    (hd : topologicalKrullDim (Z : Set X) ≤ (d : ℕ)) : IsPsEff (M.pull (redι Z)) := by
  letI := algebraΓAlong k (redι Z)
  have := isIntegral_red hZ
  obtain ⟨B, hB⟩ := exists_isAmpleLB_of_isProjOver hX
  have : IsProper (strHom k (X := X)) := by
    obtain ⟨N, i, hi, e⟩ := hX
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hA := hB.pull_of_isClosedImmersion (redι Z)
  have : IsProper (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    rw [← comp_strHom (appTop_algebraMap_along k (redι Z))]
    infer_instance
  have hN := hM.pull_of_isClosedImmersion (redι Z) (appTop_algebraMap_along k (redι Z))
  refine ⟨hN.isLB, _, hA, fun m _ => ?_⟩
  have hP := H _ (hA.isProjOver _) ((topologicalKrullDim_red Z).trans_le hd) _ _ hA (hN.pow hA m)
  obtain ⟨r, hr, hg⟩ := hP.exists_isGenerated_pow
  refine ⟨r, hr, hg.hasNonzeroSec.of_cls_eq
    (isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB m) hA.isLB) r) hg.isLB ?_⟩
  rw [cls_lbPow (isLB_tens (isLB_lbPow hN.isLB m) hA.isLB), cls_lbPow hP.isLB,
    cls_tens (isLB_lbPow hN.isLB m) hA.isLB, cls_tens hA.isLB (isLB_lbPow hN.isLB m), add_comm]

end GlobalTheory
