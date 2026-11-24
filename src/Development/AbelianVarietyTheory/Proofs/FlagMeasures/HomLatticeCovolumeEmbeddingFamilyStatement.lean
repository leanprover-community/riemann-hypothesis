module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HomLatticeCovolumeEmbeddingFamily
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.homLatticeCovolume_embedding_family : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ (r s : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin s → E)), Submodule.IsFullLattice E Λ → Submodule.IsFullLattice E Λ' → ∀ (G : ι → Matrix (Fin r) (Fin r) ℂ) (G' : ι → Matrix (Fin s) (Fin s) ℂ), (∀ v, (G v).det ≠ 0) → (∀ v, (G' v).det ≠ 0) → ∀ L : Submodule ℤ (ι → Fin r → Fin s → ℂ), (∀ z, z ∈ L ↔ ∃ T : Matrix (Fin r) (Fin s) E, (∀ y ∈ Λ', T *ᵥ y ∈ Λ) ∧ ∀ v, Matrix.of (z v) = G v * T.map (φ v) * (G' v)⁻¹) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = (covStd r Λ * ∏ v, ‖(G v).det‖ ^ 2) ^ s * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * s) / (covStd s Λ' * ∏ v, ‖(G' v).det‖ ^ 2)) ^ r := by
  first | exact @GlobalTheory.HomCovolumeFamily.homCovolume_family | exact GlobalTheory.HomCovolumeFamily.homCovolume_family | (intros; apply GlobalTheory.HomCovolumeFamily.homCovolume_family <;> first | assumption | exact Submodule.IsFullLattice.toIsLattice)
