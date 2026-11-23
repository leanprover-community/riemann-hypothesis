module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyReindexed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

theorem _root_.GlobalTheory.T.arith_variety_reindexed : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ (Gf : GenFibre (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (mCoordIdeal y)) (ch : ∀ k : FibreBlock bk, J k.1), (∀ k : FibreBlock bk, Gf.x' ⟨k.1, ch k⟩ ≠ 0) ∧ Module.finrank Gf.Φ (IntermediateField.adjoin Gf.Φ (Set.range fun q : Σ k : FibreBlock bk, J k.1 => Gf.x' ⟨q.1.1, q.2⟩ / Gf.x' ⟨q.1.1, ch q.1⟩)) = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | exact GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree <;> assumption)
