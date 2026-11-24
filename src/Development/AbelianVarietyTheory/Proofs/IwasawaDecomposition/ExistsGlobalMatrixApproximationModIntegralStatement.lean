module

public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalMatrixApproximationModIntegral
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.exists_global_matrix_approximation_mod_integral : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)] [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)] {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q), (∀ q, Irreducible (π q)) → ∀ (t : F), (∀ q, f q t = algebraMap (W q) (Q q) (π q)) → (∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z)) → ∀ {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)), (∀ q, IsUnit (g q).det) → ∀ (q0 : ι), ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧ B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧ ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) := by
  first | exact @GlobalTheory.GlobApx.exists_glob_approx | exact GlobalTheory.GlobApx.exists_glob_approx | (intros; apply GlobalTheory.GlobApx.exists_glob_approx <;> assumption)
