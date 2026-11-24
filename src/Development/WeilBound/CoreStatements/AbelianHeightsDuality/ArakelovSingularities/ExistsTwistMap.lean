module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
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
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace LBIso IsProjOver)
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.Amb

theorem exists_twist_map {k : Type} [CommRing k] {X : Scheme.{0}} {n : ℕ} (e : X ⟶ PSpace k n) [IsClosedImmersion e]
    (M : LB X) (hM : M.IsLB) :
    ∃ (t r : ℕ) (g : X ⟶ PSpace k r), g ≫ PSpace.str k r = e ≫ PSpace.str k n ∧
      cls ((O1 k r).pull g) (LB.isLB_pull (O1_isLB k r) g) =
        cls M hM + (t : ℤ) • cls ((O1 k n).pull e) (LB.isLB_pull (O1_isLB k n) e) := by
  have hO : ((O1 k n).pull e).IsLB := LB.isLB_pull (O1_isLB k n) e
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated k X (e ≫ PSpace.str k n) ((O1 k n).pull e) n _ hO
    (veryAmpleBy_secPull_coord e) M hM
  obtain ⟨r, u, hu⟩ := ht (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  refine ⟨t₀.toNat, r, toProj (e ≫ PSpace.str k n) u hu, toProj_str _ _ _, ?_⟩
  have hT : (tw M ((O1 k n).pull e) (t₀.toNat : ℤ)).IsLB := LB.isLB_div hM (isLB_pw hO _)
  rw [(cls_eq_iff _ hT).2 (lbIso_pullback_O1_toProj _ u hu)]
  refine (cls_div hM (isLB_pw hO _) hT).trans ?_
  rw [GlobalTheory.EffBound.cls_pw hO, neg_smul, sub_neg_eq_add]

end GlobalTheory.Amb
