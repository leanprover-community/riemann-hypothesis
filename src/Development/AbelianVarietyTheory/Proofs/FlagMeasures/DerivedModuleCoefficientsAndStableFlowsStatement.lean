module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlows
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.derivedModule_coefficients_and_stable_flows : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsURepOn (UJset ε) σ → IsDer ε σ V E → (∀ (w : List (Fin n × Fin n)) (v : V) (y : H), ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪y, σ x (v : H)⟫_ℂ) g = ⟪y, σ g (ew E w v : V)⟫_ℂ) ∧ (∀ W : Submodule ℂ V, FiniteDimensional ℂ W → (KStable ε E W ↔ IsKStableOn ε σ (W.map V.subtype))) ∧ ∀ (μ : Fin n → ℝ) (v : V), IsWeight E μ v ↔ IsWtOn (Kset ε) σ μ (v : H) := by
  first | exact @GlobalTheory.Jet.Coef.coef_flow | exact GlobalTheory.Jet.Coef.coef_flow | (intros; apply GlobalTheory.Jet.Coef.coef_flow <;> assumption)
