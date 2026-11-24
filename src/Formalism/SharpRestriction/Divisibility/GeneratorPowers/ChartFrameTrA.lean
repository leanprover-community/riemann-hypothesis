module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLineBundlePowerIsoGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem glue_units {X : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by
  apply GlobalTheory.RigNorm.glue_units <;> assumption

theorem exists_ratio_gen {X : Scheme.{0}} {M : LB X} (hcov : ∀ x : X, ∃ i, x ∈ M.U i) {g₁ g₂ : LB.Gen M}
    (h₁ : g₁.IsGen) (h₂ : g₂.IsGen) : ∃ u : Γ(X, ⊤)ˣ, ∀ i, g₁.s i = res (le_top : M.U i ≤ ⊤) u * g₂.s i := by
  unfold LB.Gen.IsGen at h₁ h₂
  obtain ⟨u, hu⟩ := glue_units M.U hcov (fun i => g₁.s i / g₂.s i) (fun i j => by
    rw [map_div, map_div, h₁ i j, h₂ i j, mul_div_mul_left_eq_div])
  exact ⟨u, fun i => by rw [hu i, div_mul_cancel]⟩

theorem unit_eq_one_of_eSec (hGF : GlobalFnsSt) {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (u : Γ(A.left, ⊤)ˣ) (h : (eSec A).appTop.hom u.val = 1) : u = 1 := by
  unfold GlobalFnsSt at hGF
  have hsec : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    rw [Over.w]
    rfl
  obtain ⟨s, hs⟩ := (hGF S A hA).2 u.val
  have h2 : (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s = s := by
    rw [hsec]
    simp
  have hs1 : s = 1 := by
    calc s = (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s := h2.symm
      _ = (Scheme.Hom.appTop (eSec A)).hom ((Scheme.Hom.appTop A.hom).hom s) := rfl
      _ = 1 := by rw [hs, h]
  ext
  rw [← hs, hs1, map_one]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
