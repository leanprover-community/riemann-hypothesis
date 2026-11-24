module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicU

theorem eventually_vecLoc_mem_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) (y : Fin n → Af F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, vecLoc v y ∈ latLoc F L v := by
  letI := hL
  haveI := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_latLoc_eq F L (stdLattice E n),
    Filter.eventually_all.2 fun i => eventually_map_evalV_mem_intLoc (y i)] with v h h1
  rw [h, mem_latLoc_stdLattice]
  exact h1

theorem indicator_latHat_eq_finprod :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E,
      {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator
        (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  intro F E _ _ _ _ _ n L hL X
  have key : ∀ v : HeightOneSpectrum (𝓞 F), vecLoc v (X 0) ∈ latLoc F L v →
      {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) = 1 := fun v hv =>
    Set.indicator_of_mem (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
  by_cases h : X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))
  · rw [Set.indicator_of_mem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h,
      finprod_congr fun v => key v ((mem_latHat_iff hL.fg _).1 h v), finprod_one]
    rfl
  · rw [Set.indicator_of_notMem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h]
    rw [mem_latHat_iff hL.fg, not_forall] at h
    obtain ⟨v, hv⟩ := h
    refine (finprod_eq_zero _ v ?_ ?_).symm
    · exact Set.indicator_of_notMem
        (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
    · exact Set.Finite.subset (Filter.eventually_cofinite.1 (eventually_vecLoc_mem_latLoc L hL (X 0)))
        fun u hu hu' => hu (key u hu')

end GlobalTheory.AdelicU
