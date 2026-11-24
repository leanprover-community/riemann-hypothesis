module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
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

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → perp L Hm (perp L Hm (Submodule.span E (Set.range y))) = (Submodule.span E (Set.range y)) ∧ (∀ v, (∀ x ∈ Λ, x ∈ perp L Hm (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ (Submodule.span E (Set.range y))) ∧ (∀ v, (∀ x ∈ Λ, x ∈ (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ perp L Hm (Submodule.span E (Set.range y))) ∧ ∃ b : Fin m → Fin n → E, ∃ c : Fin m → Fin n → E, Λ ⊓ (Submodule.span E (Set.range y)).restrictScalars L.O = Submodule.span L.O (Set.range b) ∧ (∀ j, c j ∈ Λ) ∧ ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.HL.DualInter.dual_inter | exact GlobalTheory.HL.DualInter.dual_inter | (intros; apply GlobalTheory.HL.DualInter.dual_inter <;> assumption)
