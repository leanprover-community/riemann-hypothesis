module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNatBoundLocalLatticesStandardAe
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

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_nat_bound_localLattices_standard_ae : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)), {p | Λ p ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite → (∀ p, ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (m : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O) → ∃ N : ℕ, N ≠ 0 ∧ ∀ p, (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (N : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (N : (A.loc p).Ep) * v i ∈ (A.L p).O := by
  first | exact @GlobalTheory.HL.Glue.exists_uniform_bound | exact GlobalTheory.HL.Glue.exists_uniform_bound | (intros; apply GlobalTheory.HL.Glue.exists_uniform_bound <;> assumption)
