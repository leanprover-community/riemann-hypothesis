module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevInequalityAtOneIndefiniteUnitary
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.sobolev_inequality_at_one_indefiniteUnitary : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ F : List (Mx n) → Mx n → ℂ, (∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)) → IsDerFam ε F → (∀ l ∈ S, Integrable (fun g : UJ ε => ‖F l (umat g)‖ ^ 2) (muG ε)) → ‖F [] 1‖ ^ 2 ≤ C * (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum := by
  first | exact @GlobalTheory.SobolevHaar.sobolev_at_one | exact GlobalTheory.SobolevHaar.sobolev_at_one | (intros; apply GlobalTheory.SobolevHaar.sobolev_at_one <;> assumption)
