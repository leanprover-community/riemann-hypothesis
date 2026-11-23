module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocal
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

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.indicator_completedLattice_eq_finprod_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E, {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X = ∏ᶠ v : HeightOneSpectrum (𝓞 F), {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  first | exact @GlobalTheory.AdelicU.indicator_latHat_eq_finprod | exact GlobalTheory.AdelicU.indicator_latHat_eq_finprod | (intros; apply GlobalTheory.AdelicU.indicator_latHat_eq_finprod <;> first | assumption | exact Submodule.IsFullLattice.toIsLattice)
