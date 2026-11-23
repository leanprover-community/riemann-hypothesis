module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle

@[expose] public section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem hilbert90_locallyConstant_cocycle :
    ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : (Ω ≃ₐ[K] Ω) → Ωˣ),
      IsLocallyConstant w → (∀ g h, ((w (g * h) : Ωˣ) : Ω) = w g * g (w h)) →
        ∃ t : Ωˣ, ∀ g, ((w g : Ωˣ) : Ω) = g t / t := by
  intro K Ω _ _ _ _ _ w hw hc
  have h1 : w 1 = 1 := by
    apply Units.ext
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    have h' : ((w 1 : Ωˣ) : Ω) * 1 = (w 1 : Ω) * (w 1 : Ω) := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ (w 1).ne_zero h').symm
  have hopen : IsOpen (w ⁻¹' {1}) := hw _
  obtain ⟨E, hfin, hE⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 (hopen.mem_nhds (by simp [h1]))
  haveI := hfin
  obtain ⟨β, hβ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_units_of_cocycle (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) (fun h => w h.1) E
    (fun h hh => hE hh) (fun g h => Units.ext (by simp [hc]))
  refine ⟨β, fun g => ?_⟩
  have := congrArg Units.val (hβ ⟨g, Subgroup.mem_top g⟩)
  simpa [div_eq_mul_inv] using this

end GlobalTheory
