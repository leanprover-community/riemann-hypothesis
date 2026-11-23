module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameParahoric

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val_lt (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem val_det_sub_one_lt {m : Type} [Fintype m] [LinearOrder m] (A : Matrix m m 𝒪[k])
    (hl : ∀ i j, j < i → valuation k (algebraMap 𝒪[k] k (A i j)) < 1)
    (hd : ∀ i, valuation k (algebraMap 𝒪[k] k (A i i) - 1) < 1) :
    valuation k ((A.map (algebraMap 𝒪[k] k)).det - 1) < 1 := by
  have h1 : (A.map (IsLocalRing.residue 𝒪[k])).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have := (residue_eq_zero_iff_val_lt (A i i - 1)).2 (by simpa using hd i)
      rw [map_sub, map_one, sub_eq_zero] at this
      simpa using this
    · intro i j hij
      exact (residue_eq_zero_iff_val_lt _).2 (hl i j hij)
  have h2 : IsLocalRing.residue 𝒪[k] (A.det - 1) = 0 := by
    rw [map_sub, map_one, RingHom.map_det, sub_eq_zero]
    simpa using h1
  have := (residue_eq_zero_iff_val_lt _).1 h2
  rwa [map_sub, map_one, RingHom.map_det] at this

theorem isIwVec_of_isParahoricVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V) (hχ : IsTame χ) (hv : IsParahoricVec χ π v) :
    IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  have hlt : ∀ (i : Fin t) (j : Fin r), Fin.castAdd t j < Fin.natAdd r i := by
    intro i j
    rw [Fin.lt_iff_val_lt_val]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    omega
  refine ⟨fun h hK hl hd => ?_, fun s hs => ?_⟩
  · obtain ⟨h₀, hh⟩ := hK
    have hval : ∀ i j, h.val i j = algebraMap 𝒪[k] k (h₀.val i j) := by
      intro i j
      rw [← hh]
      rfl
    have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) =
        (h₀.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).map (algebraMap 𝒪[k] k) := by
      ext i j
      simp [hval]
    have hdet : valuation k ((h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
      rw [hsub]
      refine val_det_sub_one_lt _ (fun i j hij => ?_) (fun i => ?_)
      · simpa [hval] using hl (Fin.natAdd r i) (Fin.natAdd r j) (by simpa using hij)
      · simpa [hval] using hd (Fin.natAdd r i)
    have hne : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hdet
      exact lt_irrefl _ hdet
    have hu : χ (Units.mk0 _ hne) = 1 := hχ _ (by simpa using hdet)
    rw [hv h ⟨h₀, hh⟩ (fun i j => hl _ _ (hlt i j)) (Units.mk0 _ hne) rfl, hu]
    simp
  · have hD : ((∏ j : Fin t, s (Fin.natAdd r j) : kˣ) : k) =
        ((diagT k (Fin (r + t)) s).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
      rw [val_diagT, Matrix.submatrix_diagonal _ _ (Fin.natAdd_injective _ _), Matrix.det_diagonal]
      simp [Units.coe_prod]
    have hlow : ∀ (i : Fin t) (j : Fin r),
        valuation k ((diagT k (Fin (r + t)) s).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1 := by
      intro i j
      rw [val_diagT, Matrix.diagonal_apply_ne _ (hlt i j).ne']
      simp
    rw [hv _ (iwahori_le_KO k (Fin (r + t)) (diagT_mem_iwahori hs)) hlow _ hD]
    congr 2
    rw [torusChar_apply, Fin.prod_univ_add, map_prod]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.TameParahoric
