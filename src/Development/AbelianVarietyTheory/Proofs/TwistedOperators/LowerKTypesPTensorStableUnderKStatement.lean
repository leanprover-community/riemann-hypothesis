module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerKTypesPTensorStableUnderK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.lowerKTypes_pTensor_stable_under_K : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), LowData ε E Λ u j → IsTau ε Λ τ w → TauTie ε E j τ → ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ k ∈ Kset ε, ∃ G' : Fin n × Fin n → W, arr1 j G' ∈ Vminus ε E Λ u ∧ ∑ p, ⟪τ k w, G p⟫_ℂ • (k⁻¹ * thE ε p * k) = ∑ p, ⟪w, G' p⟫_ℂ • thE ε p := by
  first | exact @GlobalTheory.SphJet.vminus_stable_under_K | exact GlobalTheory.SphJet.vminus_stable_under_K | (intros; apply GlobalTheory.SphJet.vminus_stable_under_K <;> assumption)
