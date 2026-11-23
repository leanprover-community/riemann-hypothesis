module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

theorem crysRed_pull_constMor_pull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).pull ((constMor A₀).pull c) = c := by
  rw [GrpMor.pull_pull (constMor A₀) (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀)
    (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun _ ↦ rfl) (by simp) c]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)



theorem mem_Fil_iff_exists_graphFil_corr (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : HdR A₀ →ₗ[k] HdR A₀) (y : HdR A₀) :
    y ∈ Fil A₀ ↔ ∃ d ∈ graphFil A₀ f,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).Corr d y := by
  constructor
  · intro hy
    obtain ⟨d, hd⟩ := exists_crys hA y (f y)
    refine ⟨d, ⟨y, hy, 0, zero_mem _, fun c ↦ by rw [hd c]; simp⟩, fun c ↦ ?_⟩
    obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TrivSqZeroExt.fst_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, TrivSqZeroExt.fst_add]
    | tmul a c =>
      rw [liftSemi_tmul, map_smulₛₗ, map_smul, crysRed_pull_constMor_pull, map_smul, hd c]
      simp
  · rintro ⟨d, ⟨x, hx, y', -, e⟩, hc⟩
    have : y = x := LinearMap.ext fun c ↦ by
      have h1 := hc ((constMor A₀).pull c)
      rw [crysRed_pull_constMor_pull, e c] at h1
      simpa using h1
    exact this ▸ hx

end GlobalTheory.HTRealise
