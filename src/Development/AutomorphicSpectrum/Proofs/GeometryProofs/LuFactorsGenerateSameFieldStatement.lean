module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuFactorsGenerateSameField
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

@[expose] public section


theorem _root_.GlobalTheory.T.lu_factors_generate_same_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (A : Matrix (Fin n) (Fin n) K) (u v w : Matrix (Fin n) (Fin n) L), A.det ≠ 0 → (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) → (∀ k, v k k = 1) → (∀ l k, l < k → v l k = 0) → (∀ l k, k < l → w l k = 0) → (∀ k, w k k ≠ 0) → A.map (algebraMap K L) * u = v * w → IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) = IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
  first | exact @GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | exact GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | (intros; apply GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq <;> assumption)
