module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
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
import Mathlib.Tactic.Linter.Style
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

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic
open GlobalTheory.ProjSpace (O1 O1_isLB)
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.Amb

theorem isSeparated_pr_zero (k : Type) [CommRing k] (m : ℕ) (n : Fin (m + 1) → ℕ) :
    IsSeparated (pr k m n 0) := by
  have hs : IsSeparated (pr k m n 0 ≫ toSpecBase k (n 0)) := by
    rw [pr_toSpecBase]
    infer_instance
  exact IsSeparated.of_comp _ (toSpecBase k (n 0))

theorem lbIso_pull_tw {k : Type} [CommRing k] {X P : Scheme.{0}} (i : X ⟶ P) {a b : ℕ} (π₁ : P ⟶ PSpace k a)
    (π₀ : P ⟶ PSpace k b) (g : X ⟶ PSpace k a) (e : X ⟶ PSpace k b) (hg : i ≫ π₁ = g) (he : i ≫ π₀ = e) (t : ℕ)
    (M : LB X) (hM : M.IsLB)
    (h : cls ((O1 k a).pull g) (LB.isLB_pull (O1_isLB k a) g) =
      cls M hM + (t : ℤ) • cls ((O1 k b).pull e) (LB.isLB_pull (O1_isLB k b) e)) :
    LBIso ((tw ((O1 k a).pull π₁) ((O1 k b).pull π₀) (-(t : ℤ))).pull i) M := by
  have hA := LB.isLB_pull (O1_isLB k a) π₁
  have hB := LB.isLB_pull (O1_isLB k b) π₀
  have hT := isLB_tw hA hB (-(t : ℤ))
  have hTi := LB.isLB_pull hT i
  rw [← cls_eq_iff hTi hM, cls_pull hT i hTi]
  have hct : cls (tw ((O1 k a).pull π₁) ((O1 k b).pull π₀) (-(t : ℤ))) hT =
      cls ((O1 k a).pull π₁) hA - (-(-(t : ℤ))) • cls ((O1 k b).pull π₀) hB := by
    show cls (((O1 k a).pull π₁).div (AbLaw.pw ((O1 k b).pull π₀) (-(-(t : ℤ))))) hT = _
    rw [cls_div hA (isLB_pw hB _) hT, EffBound.cls_pw hB]
  rw [hct, map_sub, map_zsmul, cls_pull (O1_isLB k a) π₁ hA, cls_pull (O1_isLB k b) π₀ hB,
    ← pull_comp, ← pull_comp, hg, he]
  rw [cls_pull (O1_isLB k a) g, cls_pull (O1_isLB k b) e] at h
  rw [h, neg_neg]
  abel

end GlobalTheory.Amb
