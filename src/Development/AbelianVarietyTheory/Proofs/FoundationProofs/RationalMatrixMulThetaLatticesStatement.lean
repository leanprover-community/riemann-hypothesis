module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalMatrixMulThetaLattices
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

theorem _root_.GlobalTheory.T.rationalMatrixMul_thetaLattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), (∀ i j, IsIntegral ℤ (M' i j)) → (∀ i j, IsIntegral ℤ (M i j)) → ∀ x ∈ La0 D (tor0 D cc δ) N N', mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ La0 D (tor0 D cc δ) N N', m • mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → Moves D (γA : GL (Fin N) (AE D)) L₁ → Moves D (γA' : GL (Fin N') (AE D)) L₁' → ∀ x, x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  first | exact @GlobalTheory.ThetaStab.mulV_theta_lattices | exact GlobalTheory.ThetaStab.mulV_theta_lattices | (intros; apply GlobalTheory.ThetaStab.mulV_theta_lattices <;> assumption)
