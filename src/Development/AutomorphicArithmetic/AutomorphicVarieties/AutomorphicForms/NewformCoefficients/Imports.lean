module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open UpperTheory.V in
theorem UpperTheory.V.Af.Nf.split :
    UpperTheory.V.Af.Nf.Split := by
  intro F _ _ _ a φ hφ hmem
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hmem
  have hst : ∀ t : Finset (TR.CuspSub F a), TR.IsStable (⨆ π ∈ t, π.V) := by
    intro t o x hx
    have : (⨆ π ∈ t, π.V) ≤ (⨆ π ∈ t, π.V).comap (TR.act o) :=
      iSup₂_le fun π hπ y hy =>
        (le_iSup₂ (f := fun (π : TR.CuspSub F a) (_ : π ∈ t) => π.V) π hπ) (π.stable o y hy)
    exact this hx
  induction s using Finset.induction_on with
  | empty => exact absurd (by simpa using hs) hφ
  | insert π t _ ih =>
    by_cases ht : φ ∈ ⨆ π ∈ t, π.V
    · exact ih ht
    rw [Finset.iSup_insert] at hs
    obtain ⟨ψ, hψ, w, hw, e⟩ := Submodule.mem_sup.1 hs
    rcases π.irred (π.V ⊓ ⨆ π ∈ t, π.V) inf_le_left
      (fun o x hx => ⟨π.stable o x hx.1, hst t o x hx.2⟩) with h | h
    · refine ⟨π, ⟨ψ, hψ⟩, _, ?_, hst t, disjoint_iff.2 h, ?_⟩
      · intro h0
        have h1 : ψ = 0 := congrArg Subtype.val h0
        rw [h1, zero_add] at e
        exact ht (e ▸ hw)
      · rw [← e]
        simpa using hw
    · exact absurd (e ▸ Submodule.add_mem _ (inf_eq_left.1 h hψ) hw) ht
