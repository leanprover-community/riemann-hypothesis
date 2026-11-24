module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternUnitriangularStrongApproximation
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

theorem _root_.GlobalTheory.T.pattern_unitriangular_strong_approximation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  first | exact @GlobalTheory.HL.pattern_strong_approx | exact GlobalTheory.HL.pattern_strong_approx | (intros; apply GlobalTheory.HL.pattern_strong_approx <;> assumption)
