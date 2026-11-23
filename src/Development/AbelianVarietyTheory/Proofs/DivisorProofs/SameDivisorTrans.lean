module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

private theorem resG_resG_sameDiv {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem SameDiv.trans_of_isLB : ∀ (X : Scheme.{0}) (L M N : LB X) (σ : L.Sec) (τ : M.Sec) (υ : N.Sec),
    M.IsLB → SameDiv σ τ → SameDiv τ υ → SameDiv σ υ := by
  intro X L M N σ τ υ _ h₁ h₂ x
  obtain ⟨U₁, i, j, hi, hj, u₁, hx₁, e₁⟩ := h₁ x
  obtain ⟨U₂, j', k, hj', hk, u₂, hx₂, e₂⟩ := h₂ x
  have hV : U₁ ⊓ U₂ ≤ M.U j ⊓ M.U j' := le_inf (inf_le_left.trans hj) (inf_le_right.trans hj')
  have c := congrArg (resG X hV) (τ.compat j j')
  have e₁' := congrArg (resG X (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) e₁
  have e₂' := congrArg (resG X (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) e₂
  change resG X hV (resG X inf_le_left (τ.f j)) =
    resG X hV ((M.g j j' : Γ(X, M.U j ⊓ M.U j')) * resG X inf_le_right (τ.f j')) at c
  simp only [map_mul, resG_resG_sameDiv] at c e₁' e₂'
  refine ⟨U₁ ⊓ U₂, i, k, inf_le_left.trans hi, inf_le_right.trans hk,
    res inf_le_left u₁ * res hV (M.g j j') * res inf_le_right u₂, ⟨hx₁, hx₂⟩, ?_⟩
  simp only [Units.val_mul, res, Units.coe_map, MonoidHom.coe_coe]
  rw [e₁', c, e₂']
  simp only [resG, mul_assoc]

end GlobalTheory.LogPair
