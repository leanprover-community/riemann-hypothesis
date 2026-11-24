module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDenominator
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ProperDenom

variable {M W : Scheme.{0}}

end GlobalTheory.ProperDenom

namespace GlobalTheory.ProperDenom

theorem exists_local_denom : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] [IsProper f] [IsLocallyNoetherian W] (L : LB M), IsAmpleLB L → ∀ {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) → ∀ y : W, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧ ∀ y' ∈ V, ∀ (V' : W.Opens), y' ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y' (fnOf V (gen_mem hy) d * co j (fnOf (f ⁻¹ᵁ V') h z)) := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator
  | exact _root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator
  | (apply _root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistenceLemmas.exists_local_denominator ..)

end GlobalTheory.ProperDenom
