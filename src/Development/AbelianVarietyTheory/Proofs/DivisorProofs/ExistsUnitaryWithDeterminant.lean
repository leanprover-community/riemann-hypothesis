module

public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.UnitDet

theorem exists_imag (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ ξ : E, ξ ≠ 0 ∧ IsCMField.complexConj E ξ = -ξ := by
  obtain ⟨t, ht⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  refine ⟨t - IsCMField.complexConj E t, sub_ne_zero.2 (fun h => ht h.symm), ?_⟩
  simp [IsCMField.complexConj_apply_apply]

theorem herm_single {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.single_apply, apply_ite, ite_mul]

theorem exists_aniso {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {G : Matrix (Fin r) (Fin r) E} (hdet : G.det ≠ 0) (hr : 0 < r) :
    ∃ e : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G e e ≠ 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨ξ, hξ0, hξ⟩ := exists_imag E
  have h0 : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm G x y = 0 := by
    intro x y
    have h1 := hne (x + (1:E) • y)
    have h2 := hne (x + ξ • y)
    rw [GlobalTheory.FlagData.herm_add_smul_left, GlobalTheory.FlagData.herm_add_smul_right,
      GlobalTheory.FlagData.herm_add_smul_right, hne x, hne y] at h1 h2
    simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_one, hξ] at h1 h2
    have h3 : (-2 * ξ) * ReciprocityTheory.ChartRestriction.G.FD.herm G x y = 0 := by linear_combination h2 - ξ * h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (by simpa using hξ0)
    · exact h
  apply hdet
  have hG0 : G = 0 := by
    ext a b
    rw [← herm_single G a b, h0]
    rfl
  rw [hG0]
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (u : E), 0 < r → (∀ a b, IsCMField.complexConj E (G a b) = G b a) → G.det ≠ 0 → u * IsCMField.complexConj E u = 1 → ∃ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧ (γ : Matrix (Fin r) (Fin r) E).det = u := by
  intro E _ _ _ r G u hr hG hdet hu
  obtain ⟨e, he⟩ := exists_aniso hdet hr
  have hG' : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := hG
  have hch : IsCMField.complexConj E (ReciprocityTheory.ChartRestriction.G.FD.herm G e e) = ReciprocityTheory.ChartRestriction.G.FD.herm G e e :=
    GlobalTheory.FlagData.cc_herm hG' e e
  set h := ReciprocityTheory.ChartRestriction.G.FD.herm G e e with hh
  set α : E := (u - 1) / h with hα
  have hdetT : (ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α).det = u := by
    set v : Fin r → E := fun b => α * ∑ k, G b k * ReciprocityTheory.ChartRestriction.G.FD.cc (e k) with hv
    have hT : ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α = 1 + replicateCol (Fin 1) e *
        replicateRow (Fin 1) v := by
      ext a b
      simp [ReciprocityTheory.ChartRestriction.G.FD.transvMat, replicateCol, replicateRow, Matrix.mul_apply, Matrix.one_apply]
      ring
    have hd := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) e v
    rw [hT]
    refine hd.trans ?_
    have : v ⬝ᵥ e = α * h := by
      rw [hh, hv]
      simp only [dotProduct, ReciprocityTheory.ChartRestriction.G.FD.herm, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, hα]
    field_simp
    ring
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have key : IsCMField.complexConj E α + α + α * IsCMField.complexConj E α * h = 0 := by
    have hca : IsCMField.complexConj E α = (IsCMField.complexConj E u - 1) / h := by
      rw [hα, map_div₀, map_sub, map_one, hch]
    rw [hca, hα]
    field_simp
    linear_combination hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdetT ▸ hu0), ?_, ?_⟩
  · intro x y
    show ReciprocityTheory.ChartRestriction.G.FD.herm G (ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α *ᵥ x)
      (ReciprocityTheory.ChartRestriction.G.FD.transvMat G e α *ᵥ y) = ReciprocityTheory.ChartRestriction.G.FD.herm G x y
    rw [GlobalTheory.FlagData.transvMat_mulVec, GlobalTheory.FlagData.transvMat_mulVec, GlobalTheory.FlagData.herm_add_smul_left,
      GlobalTheory.FlagData.herm_add_smul_right, GlobalTheory.FlagData.herm_add_smul_right]
    have e1 : ReciprocityTheory.ChartRestriction.G.FD.cc (α * ReciprocityTheory.ChartRestriction.G.FD.herm G y e) =
        IsCMField.complexConj E α * ReciprocityTheory.ChartRestriction.G.FD.herm G e y := by
      rw [← GlobalTheory.FlagData.cc_herm hG' y e]
      exact map_mul (IsCMField.complexConj E) _ _
    rw [e1, ← hh]
    linear_combination (ReciprocityTheory.ChartRestriction.G.FD.herm G x e * ReciprocityTheory.ChartRestriction.G.FD.herm G e y) * key
  · exact hdetT

end GlobalTheory.UnitDet
