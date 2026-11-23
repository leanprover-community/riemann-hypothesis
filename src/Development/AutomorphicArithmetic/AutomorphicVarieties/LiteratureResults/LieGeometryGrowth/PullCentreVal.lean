module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

private theorem span_val {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ} (P : Sm E a → Prop)
    (x y : GA E a) (c : ℂ) (h : ∀ φ, P φ → φ.1 x = c * φ.1 y) (m : Sm E a ⊗[ℂ] (Fin d → ℂ))
    (hm : m ∈ Submodule.span ℂ {z : Sm E a ⊗[ℂ] (Fin d → ℂ) | ∃ φ v, P φ ∧ z = φ ⊗ₜ[ℂ] v}) : ev m x = c • ev m y := by
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨φ, v, hφ, rfl⟩ := hz
    rw [ev_tmul, ev_tmul, h φ hφ, mul_smul]
  | zero => simp
  | add z w _ _ hz hw => simp only [map_add (f := _), Pi.add_apply, hz, hw, smul_add]
  | smul s z _ hz => simp only [map_smul, Pi.smul_apply, hz, smul_comm s c]

theorem UpperTheory.V.Lit.Geo.centreVal :
    CentreVal := by
  intro E _ _ _ a U Ξ r hr q α hα X γ t g
  refine span_val (IsLevelFn U Ξ) _ _ _ (fun φ hφ => ?_) _ (hα.3 X)
  rw [mul_assoc, hφ.1, aInv E a φ _ (hφ.2.2 r hr), neg_mul]
