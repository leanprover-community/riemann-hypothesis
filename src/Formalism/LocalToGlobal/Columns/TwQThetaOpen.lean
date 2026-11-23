module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

def lqPrinc (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ i j : Fin n, P.valuation E ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) ≤
    WithZero.coe (Multiplicative.ofAdd (-(N : ℤ)))

def ThetaOpen {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) : Prop :=
  ∀ P : Q, ∃ N : ℕ, 0 < N ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N (g : Sp E n ≃ₗ[E] Sp E n) →
    ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1

theorem thetaOpen_top (Q : Finset (HeightOneSpectrum (𝓞 E))) : ThetaOpen (LevQFam.top E K n Q) := by
  intro P
  exact ⟨1, Nat.one_pos, fun g _ => ⟨Subgroup.mem_top _, rfl⟩⟩

end Formalism.L2.Col
