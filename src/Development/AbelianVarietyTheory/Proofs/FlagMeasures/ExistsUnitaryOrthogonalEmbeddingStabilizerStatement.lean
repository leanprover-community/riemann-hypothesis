module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n m : ℕ) (J : Matrix (Fin n) (Fin n) R) (J' : Matrix (Fin m) (Fin m) R) (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R), IsUnit ((fun i => σ (x i)) ⬝ᵥ (J *ᵥ x)) → (fun i => σ (x i)) ᵥ* (J * A) = 0 → Formalism.UG.cT σ A *ᵥ (J *ᵥ x) = 0 → Formalism.UG.cT σ A * J * A = J' → A' * A = 1 → A' *ᵥ x = 0 → u ᵥ* A = 0 → u ⬝ᵥ x = 1 → vecMulVec x u + A * A' = 1 → ∃ j : Formalism.UG.UJ σ J' →* Formalism.UG.UJ σ J, (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = vecMulVec x u + A * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * A') ∧ ∀ h : Formalism.UG.UJ σ J, ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x = x → h ∈ j.range := by
  first | exact @GlobalTheory.StabRing.exists_emb | exact GlobalTheory.StabRing.exists_emb | (intros; apply GlobalTheory.StabRing.exists_emb <;> assumption)
