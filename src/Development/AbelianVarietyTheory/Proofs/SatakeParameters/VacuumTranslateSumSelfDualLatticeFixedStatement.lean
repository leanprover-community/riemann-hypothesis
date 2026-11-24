module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumTranslateSumSelfDualLatticeFixed
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

open Matrix

theorem _root_.GlobalTheory.T.vacuumTranslateSum_selfDualLattice_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a → ∀ Z : Finset (Matrix (Fin n') (Fin n) L),
    (∀ z ∈ Z, ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
      z = u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) →
    (∀ z ∈ Z, ∀ z' ∈ Z, z - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → z = z') →
    (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ z ∈ Z, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - z ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) →
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (∑ z ∈ Z, ρ z s) = ∑ z ∈ Z, ρ z s := by
  first | exact @GlobalTheory.Hk3.HoweG.vacuum_sum_selfDual_fixed | exact GlobalTheory.Hk3.HoweG.vacuum_sum_selfDual_fixed | (intros; apply GlobalTheory.Hk3.HoweG.vacuum_sum_selfDual_fixed <;> assumption)
