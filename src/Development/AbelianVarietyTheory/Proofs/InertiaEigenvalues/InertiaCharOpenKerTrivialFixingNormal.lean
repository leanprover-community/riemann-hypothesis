module

public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem char_inertia_trivial_on_fixing_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l)
    (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) →
    ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)),
      (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 := by
  intro l _ LL χ hopen
  obtain ⟨t₁, ht₁, ht₁e⟩ := isOpen_induced_iff.mp hopen
  obtain ⟨t₂, ht₂, ht₂e⟩ := isOpen_induced_iff.mp ht₁
  have h1 : (1 : GQ l) ∈ t₂ := by
    have hk : (1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := χ.ker.one_mem
    rw [← ht₁e] at hk
    have hk' : ((1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) ∈ t₁ := hk
    rw [← ht₂e] at hk'
    exact hk'
  obtain ⟨E, hfd, hN, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) t₂).1 (ht₂.mem_nhds h1)
  refine ⟨⟨E, hfd⟩, hN, fun g hg => ?_⟩
  have hg₂ : ((g : Gl l) : GQ l) ∈ t₂ :=
    hE ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hg x hx)
  have hg₁ : (g : Gl l) ∈ t₁ := by
    rw [← ht₂e]; exact hg₂
  have hg₀ : g ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := by
    rw [← ht₁e]; exact hg₁
  exact hg₀

end GlobalTheory.InertiaEigenvalues
