module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHolomorphicLowestKTypeComplexified
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

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.exists_holomorphic_lowestKType_complexified : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) (u : V), IsURepOn (UJset ε) σ → DerTie ε σ E ι → ‖u‖ = 1 → IsKTypeOf ε σ Λ ((kSpan ε E u).map ι.toLinearMap) → IsWtOn (Kset ε) σ Λ (ι u) → ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (j : W →ₗᵢ[ℂ] V), IsTau ε Λ τ w ∧ j w = u ∧ LinearMap.range j.toLinearMap = kSpan ε E u ∧ TauTie ε E j τ := by
  first | exact @GlobalTheory.SphJet.LowTau.exists_tau | exact GlobalTheory.SphJet.LowTau.exists_tau | (intros; apply GlobalTheory.SphJet.LowTau.exists_tau <;> assumption)
