module

public import ReciprocityTheory.DualLattices.ProdPowUnitVectorVal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

section Res

variable [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]

def Lk (D : Lifts H U X) : Matrix (Ix g) (Ix g) (IsLocalRing.ResidueField R) :=
  D.Λ.map (IsLocalRing.residue R)

def Mk (D : Lifts H U X) : Matrix (Ix g) (Ix g) (IsLocalRing.ResidueField R) :=
  (Lk D).map (fun a => a ^ p) * (Lk D)⁻¹

theorem Lk_det (D : Lifts H U X) : IsUnit (Lk D).det := by
  unfold Lk
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact D.Λ_det.map _

theorem lam_p (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    lam (Lk D) j y ^ p = ∑ l, Mk D j l * lam (Lk D) l y := by
  have hinv : (Lk D)⁻¹ * Lk D = 1 := Matrix.nonsing_inv_mul _ (Lk_det D)
  have hxc : ∀ i, (xc (IsLocalRing.ResidueField R) i y) ^ p = xc (IsLocalRing.ResidueField R) i y := by
    intro i
    simp only [xc]
    rw [← map_pow, ZMod.pow_card]
  have hR : ∑ l, Mk D j l * lam (Lk D) l y =
      ((Mk D * Lk D) *ᵥ fun i => xc (IsLocalRing.ResidueField R) i y) j := by
    rw [← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, lam]
  rw [hR]
  unfold Mk
  rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  simp only [lam, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [sum_pow_char]
  simp only [mul_pow, hxc]

theorem formMonomial_unitVector (D : Lifts H U X) (l : Ix g) (y : Nb p g) :
    monF (Lk D) (e1 l) y = lam (Lk D) l y := by
  simp only [monF, e1]
  rw [Finset.prod_eq_single l]
  · simp [ZMod.val_one]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem MuR_map (hv : v.Integers R) (D : Lifts H U X) :
    (MuR hv D).map (IsLocalRing.residue R) = Matrix.of fun (y α : Nb p g) => monF (Lk D) α y := by
  ext y α
  simp [MuR, monF, Lk, residue_uR hv]

theorem res_bR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) : IsLocalRing.residue R (bR hv D j (e1 l)) = Mk D j l := by
  classical
  have hMu := MuR_mulVec_bR hv hp1 D j
  have hdet : IsUnit ((MuR hv D).map (IsLocalRing.residue R)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_det_MuR hv hp1 D).map _
  let c : Nb p g → IsLocalRing.ResidueField R := fun α => ∑ l', if α = e1 l' then Mk D j l' else 0
  have hvecres : ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ
      (fun α => IsLocalRing.residue R (bR hv D j α)) = ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ c := by
    funext y
    have h1 : ((MuR hv D).map (IsLocalRing.residue R) *ᵥ fun α => IsLocalRing.residue R (bR hv D j α)) y =
        IsLocalRing.residue R (hvec hv D j y) := by
      rw [← hMu, RingHom.map_mulVec]
      rfl
    rw [h1, hvec, map_pow, residue_uR hv]
    change lam (Lk D) j y ^ p = _
    rw [lam_p, MuR_map hv D]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, c, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, formMonomial_unitVector]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hinv := Matrix.nonsing_inv_mul _ hdet
  have hinj : (fun α => IsLocalRing.residue R (bR hv D j α)) = c := by
    calc (fun α => IsLocalRing.residue R (bR hv D j α))
        = (((MuR hv D).map (IsLocalRing.residue R))⁻¹ * (MuR hv D).map (IsLocalRing.residue R)) *ᵥ
            (fun α => IsLocalRing.residue R (bR hv D j α)) := by rw [hinv, Matrix.one_mulVec]
      _ = c := by rw [← Matrix.mulVec_mulVec, hvecres, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hc : IsLocalRing.residue R (bR hv D j (e1 l)) = c (e1 l) := congrFun hinj (e1 l)
  rw [hc]
  simp only [c]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have h2 := congrFun h l
    simp [e1, Pi.single_apply, Ne.symm hb] at h2
  · simp

theorem Mk_det (D : Lifts H U X) : (Mk D).det ≠ 0 := by
  have h0 := (Lk_det D).ne_zero
  have hfrob : (Lk D).map (fun a => a ^ p) =
      (frobenius (IsLocalRing.ResidueField R) p).mapMatrix (Lk D) := by
    ext a b
    simp [frobenius_def]
  have hdet : ((Lk D).map (fun a => a ^ p)).det = (Lk D).det ^ p := by
    rw [hfrob, ← RingHom.map_det, frobenius_def]
  unfold Mk
  rw [Matrix.det_mul, hdet, Matrix.det_nonsing_inv]
  exact mul_ne_zero (pow_ne_zero _ h0) (by simpa [Ring.inverse_eq_inv] using h0)

theorem Mk_off (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) (hl : D.κ l ≠ U.φ (D.κ j)) : Mk D j l = 0 := by
  rw [← res_bR hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero]

theorem block_det_ne (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (i : Fin U.m) (e : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}) :
    (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  let W : Ix g → IsLocalRing.ResidueField R := fun j => if hj : D.κ j = i then w ⟨j, hj⟩ else 0
  apply Mk_det D
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨W, ?_, ?_⟩
  · intro hW
    apply hw0
    funext j
    have h1 := congrFun hW j.1
    simpa [W, j.2] using h1
  · funext l
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hl : D.κ l = U.φ i
    · have h1 := congrFun hw (e.symm ⟨l, hl⟩)
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Equiv.apply_symm_apply,
        Pi.zero_apply] at h1
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => D.κ j = i)]
      have h2 : ∑ j : {j // ¬ D.κ j = i}, W j.1 * Mk D j.1 l = 0 :=
        Finset.sum_eq_zero fun j _ => by simp [W, j.2]
      have h3 : ∑ j : {j // D.κ j = i}, W j.1 * Mk D j.1 l = ∑ j, w j * Mk D j.1 l :=
        Finset.sum_congr rfl fun j _ => by simp [W, j.2]
      rw [h2, h3, add_zero]
      exact h1
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : D.κ j = i
      · rw [Mk_off hv hp1 D j l (by rw [hj]; exact hl), mul_zero]
      · simp [W, hj]

end Res

end ReciprocityTheory.PGsh.Up.UnitVectorPowers
