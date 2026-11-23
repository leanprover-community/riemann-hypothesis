module

public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorOfGeneralizedEigenUnramified
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
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.IncomingBounds.IncomingBound
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.eigenvector_of_generalized_eigen_unramified : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ d : ℕ, 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ (ψ : O →+* C) (w : κ → C), (∀ x, V.Ge 0 (ψ x)) → (∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → (∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i)) → ∀ x, (L x).mulVec w = ψ x • w := by
  first | exact @GlobalTheory.GenEigen.eigen_of_gen_eigen | exact GlobalTheory.GenEigen.eigen_of_gen_eigen | (intros; apply GlobalTheory.GenEigen.eigen_of_gen_eigen <;> assumption)
