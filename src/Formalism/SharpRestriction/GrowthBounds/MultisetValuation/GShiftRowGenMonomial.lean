module

public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwist
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
import Mathlib.Tactic.TypeStar
import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

section Grade

variable {r : ℕ} (ht : Fin r → ℤ)

def htW (n : ℕ) : Fin r × Fin n → ℤ := fun v => ht v.1

def GShift {R : Type*} [CommRing R] {n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (htW ht n) (P.coeff k) (μ + k * δ)

variable {ht}

end Grade

section Pos

theorem mem_deltaL {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ} {ν : Fin k → ℕ}
    {g : Matrix (Fin k) (Fin k) Kf} {F : MvPolynomial (Fin k × Fin k) Kf} :
    F ∈ deltaL O Kf k ν g ↔ ∃ f ∈ weyl O k k le_rfl ν, map (algebraMap O Kf) f = rowAct Kf g F := by
  unfold deltaL
  rw [Submodule.mem_comap, Submodule.mem_map]
  first
  | rfl

theorem dl_P (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m r : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ deltaLTw O Kf m lam g) :
    (algebraMap O Kf w ^ (∑ i : Fin (m + 1) with i.val < r, lam i)) • F ∈
      deltaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) :=
  Formalism.L2.G.Model.dl_P O Kf m r lam hlam w hw g F hF

theorem dl_indep (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (hs : colSpan O g = colSpan O h) : deltaLTw O Kf m lam g ≤ deltaLTw O Kf m lam h := by
  classical
  have hcol : ∀ (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), colSpan O g = colSpan O h →
      ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) O, h = g * U.map (algebraMap O Kf) := by
    intro g h hs
    have h1 : ∀ j, ∃ c : Fin (m + 1) → O, ∑ i, c i • (fun a => g a i) = fun a => h a j := by
      intro j
      have hm : (fun a => h a j) ∈ colSpan O g := by
        rw [hs]; exact Submodule.subset_span ⟨j, rfl⟩
      exact (Submodule.mem_span_range_iff_exists_fun O).1 hm
    choose c hc using h1
    refine ⟨fun i j => c j i, ?_⟩
    ext a j
    have h2 := congrFun (hc j) a
    rw [Matrix.mul_apply, ← h2, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    show c j i • g a i = g a i * algebraMap O Kf (c j i)
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨U, hU⟩ := hcol g h hs
  obtain ⟨U', hU'⟩ := hcol h g hs.symm
  have hdU : ∀ V : Matrix (Fin (m + 1)) (Fin (m + 1)) O,
      (V.map (algebraMap O Kf)).det = algebraMap O Kf V.det :=
    fun V => (RingHom.map_det (algebraMap O Kf) V).symm
  have hdet : U.det * U'.det = 1 := by
    apply hinj
    have h1 : g.det * (algebraMap O Kf U.det * algebraMap O Kf U'.det) = g.det * 1 := by
      conv_rhs => rw [mul_one, hU', hU, Matrix.det_mul, Matrix.det_mul, hdU, hdU]
      ring
    rw [map_mul, map_one]
    exact mul_left_cancel₀ hg.ne_zero h1
  let u : Oˣ := ⟨U.det, U'.det, hdet, by rw [mul_comm]; exact hdet⟩
  set e : ℤ := lam (Fin.last m) with he
  have hz : algebraMap O Kf ((u ^ e : Oˣ) : O) = (algebraMap O Kf U.det) ^ e := by
    calc algebraMap O Kf ((u ^ e : Oˣ) : O)
        = ((Units.map (algebraMap O Kf : O →* Kf) (u ^ e) : Kfˣ) : Kf) := rfl
      _ = (((Units.map (algebraMap O Kf : O →* Kf) u) ^ e : Kfˣ) : Kf) := by rw [map_zpow]
      _ = ((Units.map (algebraMap O Kf : O →* Kf) u : Kfˣ) : Kf) ^ e := Units.val_zpow_eq_zpow_val _ _
      _ = (algebraMap O Kf U.det) ^ e := rfl
  have hUne : algebraMap O Kf U.det ≠ 0 := by
    intro h0
    have := congrArg (algebraMap O Kf) hdet
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  let UU : GL (Fin (m + 1)) O := Matrix.nonsingInvUnit U u.isUnit
  intro F hF
  obtain ⟨F0, hF0, rfl⟩ := hF
  obtain ⟨f, hf, hfe⟩ := mem_deltaL.1 hF0
  have hst : rowAct O U f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam) := by
    have := _root_.Formalism.UG.P.wlocal_global O (m + 1) (m + 1) le_rfl (nuOf lam) UU⁻¹ f hf
    unfold Formalism.UG.dwAct at this
    rw [inv_inv] at this
    exact this
  refine ⟨(algebraMap O Kf U.det) ^ e • F0,
    mem_deltaL.2 ⟨((u ^ e : Oˣ) : O) • rowAct O U f, Submodule.smul_mem _ _ hst, ?_⟩, ?_⟩
  · have h4 : rowAct Kf (U.map (algebraMap O Kf)) (rowAct Kf g F0) = rowAct Kf h F0 := by
      have h5 := rowActMul Kf (m + 1) (m + 1) (U.map (algebraMap O Kf)) g
      rw [hU, ← h5]
      rfl
    rw [map_smul (rowAct Kf h), ← h4, ← hfe, ← ldtwist_map_rowAct, ← hz, algebraMap_smul]
    exact (map_smul (mapAlgHom (Algebra.ofId O Kf)).toLinearMap ((u ^ e : Oˣ) : O) (rowAct O U f))
  · show h.det ^ (-e) • ((algebraMap O Kf U.det) ^ e • F0) = g.det ^ (-e) • F0
    rw [smul_smul, hU, Matrix.det_mul, hdU, mul_zpow, mul_assoc, ← zpow_add₀ hUne, neg_add_cancel, zpow_zero, mul_one]

theorem dl_pos (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ Dl0 O m lam (colSpan O g)) :
    (algebraMap O Kf w ^ (∑ i : Fin (m + 1) with i.val < r, lam i)) • F ∈
      Dl0 O m lam (colSpan O (g * lb_D (m + 1) r (algebraMap O Kf w))) := by
  have hgD : IsUnit (g * lb_D (m + 1) r (algebraMap O Kf w)).det := by
    rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ _ hw)
  unfold Dl0 at hF ⊢
  by_cases hlam : Antitone lam
  · rw [if_pos hlam] at hF ⊢
    have h1 : F ∈ deltaLTw O Kf m lam g := (iInf₂_le g ⟨hg, rfl⟩ : _ ≤ deltaLTw O Kf m lam g) hF
    have h2 := dl_P O Kf m r lam hlam w hw g F h1
    exact (le_iInf₂ fun h hh => dl_indep O Kf hinj m lam _ h hgD hh.2 :
      deltaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) ≤ _) h2
  · rw [if_neg hlam] at hF ⊢
    rw [Submodule.mem_bot] at hF ⊢
    rw [hF, smul_zero]

end Pos

end Formalism.MainNotions.FormalGroupSystem.Pf
