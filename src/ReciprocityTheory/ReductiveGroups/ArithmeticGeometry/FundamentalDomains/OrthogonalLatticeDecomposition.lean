module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem orthogonal_lattice_decomposition : ProjectionAlongComplement (E := E) := by
  intro r X ξ hξ x hx u hu
  obtain ⟨-, hiso, hne⟩ := hξ
  have key : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.ucomp x ξ u τ) (Data.emb τ.1 ξ) = 0 ∧
      hermC τ.1 X.Gm (X.Jz x (X.ucomp x ξ u) τ) (Data.emb τ.1 ξ) = 0 := by
    intro τ
    set e := Data.emb τ.1 ξ with he
    have he0 : e ≠ 0 := emb_ne_zero τ.1 hne
    have hee : hermC τ.1 X.Gm e e = 0 := by rw [he, hermC_emb, hiso, map_zero]
    have hη : X.Hf x τ e e ≠ 0 := fun h => by
      have := X.Hf_iso_pos hx τ he0 hee
      rw [h] at this; simp at this
    have hu' : X.ucomp x ξ u τ = u τ - (X.Hf x τ (u τ) e / X.Hf x τ e e) • e := rfl
    refine ⟨?_, ?_⟩
    · rw [hu', hermC_sub_left, hermC_smul_left, hee, mul_zero, sub_zero]
      exact hu τ
    · rw [Data.Jz_apply, hu', hermC_smul_left, Data.jp_sub, Data.jp_smul, hermC_sub_left,
        hermC_smul_left, ← Data.Hf_eq_jp, ← Data.Hf_eq_jp, div_mul_cancel₀ _ hη, sub_self, mul_zero]
  exact ⟨fun τ => (key τ).1, fun τ => (key τ).2⟩

end ReciprocityTheory.ChartRestriction.G.FD
