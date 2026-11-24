module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersInvariantCompatibleFamily
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

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerCharacters_invariant_compatible_family : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ) (c : Fin (w + 1) → X.Khat l), (∀ i, c i ∈ X.A l) → (∀ γ ∈ Gam N l, ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k)) → ∃ Φ, IsFam l w (Gam N l) Φ ∧ ∀ n i, Kum X l n (c i) (fun δ => AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) := by
  first | exact @GlobalTheory.KZ.H3.kum_family | exact GlobalTheory.KZ.H3.kum_family | (intros; apply GlobalTheory.KZ.H3.kum_family <;> assumption)
