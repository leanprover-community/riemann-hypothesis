module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatioCover

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r := by
  intro A _ g L u hA
  haveI := hA.comm
  obtain ⟨H, _, m, s, hv⟩ := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA
  refine ⟨m + 1, fun k => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k),
    fun k j => GlobalTheory.ProjSpace.secRatio (s k) (s j), fun k => (hv.2 k).1, hv.1,
    fun k j => GlobalTheory.ProjSpace.basicOpen_secRatio _ _, fun k => GlobalTheory.ProjSpace.secRatio_self _, ?_⟩
  intro k j l z hk hj
  have hkj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) ⊓ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s j)) :=
    (GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨hk, hj⟩
  have e := congrArg (valAt' (u.ex z).left _)
    (GlobalTheory.ProjSpace.secRatio_mul_secRatio (s k) (s j) (s l) (inf_le_left) (inf_le_right))
  rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_res _ _ _ hkj, GlobalTheory.valAt'_res _ _ _ hkj, GlobalTheory.valAt'_res _ _ _ hkj] at e
  exact e.symm

end GlobalTheory.RatioCover
