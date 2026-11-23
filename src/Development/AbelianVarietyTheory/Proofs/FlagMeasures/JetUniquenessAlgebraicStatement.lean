module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JetUniquenessAlgebraic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.jet_uniqueness_algebraic : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (E' : Fin n → Fin n → Module.End ℂ V') (ι : V →ₗ[ℂ] V') (ev : V' →ₗ[ℂ] V), GlRel E' → (∀ c d, ε c = ε d → ∀ x ∈ kSpan ε E u, ι (E c d x) = E' c d (ι x)) → (∀ y, ev y ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ y, ev (E' c d y) = E c d (ev y)) → (∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E' a b (ι (at1 G a b)) = 0) → (∀ x ∈ kSpan ε E u, ev (ι x) = 0) → ∀ (w : List (Fin n × Fin n)), ∀ x ∈ kSpan ε E u, ev (ew E' w (ι x)) = 0 := by
  first | exact @GlobalTheory.Jet.UniqAlg.uniqAlg | exact GlobalTheory.Jet.UniqAlg.uniqAlg | (intros; apply GlobalTheory.Jet.UniqAlg.uniqAlg <;> assumption)
