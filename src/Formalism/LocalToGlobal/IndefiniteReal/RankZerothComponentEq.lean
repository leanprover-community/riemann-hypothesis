import Formalism.LocalToGlobal.IndefiniteReal.ModelConjugation
import Formalism.LocalToGlobal.IndefiniteReal.DiscreteSeriesParameterPos

noncomputable section

open Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult

namespace Formalism.IndefR.ModelConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isEnum_unique {n : ℕ} {S : SPar} {lam lam' : Fin n → ℝ} {ε ε' : Fin n → Bool}
    (h : IsEnum S lam ε) (h' : IsEnum S lam' ε') : lam = lam' ∧ ε = ε' := by
  obtain ⟨ha, q, hq, hS⟩ := h
  obtain ⟨ha', q', hq', hS'⟩ := h'
  have key : ∀ a, ∃ b, q' b = q a ∧ ε' b = ε a := by
    intro a
    have hm : (q a, ε a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS'] at hm
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hm
    exact ⟨b, congrArg Prod.fst hb, congrArg Prod.snd hb⟩
  have key' : ∀ b, ∃ a, q a = q' b := by
    intro b
    have hm : (q' b, ε' b) ∈ S := by rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
    rw [hS] at hm
    obtain ⟨a, -, hqa⟩ := Finset.mem_image.mp hm
    exact ⟨a, congrArg Prod.fst hqa⟩
  have hm1 : StrictMono fun a => OrderDual.toDual (lam a) := fun a b hab =>
    OrderDual.toDual_lt_toDual.2 (ha hab)
  have hm2 : StrictMono fun a => OrderDual.toDual (lam' a) := fun a b hab =>
    OrderDual.toDual_lt_toDual.2 (ha' hab)
  have hr : Set.range (fun a => OrderDual.toDual (lam a)) = Set.range (fun a => OrderDual.toDual (lam' a)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb, -⟩ := key a
      exact ⟨b, by simp only [hq, hq', hb]⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, hqa⟩ := key' b
      exact ⟨a, by simp only [hq, hq', hqa]⟩
  have hl : lam = lam' := by
    have := (StrictMono.range_inj hm1 hm2).mp hr
    funext a
    exact congrArg OrderDual.ofDual (congrFun this a)
  refine ⟨hl, funext fun a => ?_⟩
  obtain ⟨b, hb, he⟩ := key a
  have hab : b = a := by
    apply ha'.injective
    rw [hq' b, hb, ← hq a, hl]
  rw [← he, hab]

theorem rank_zeroth_component_eq (D : D7) : (D.sp.Y 0).rank = D.R.r := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]; simp [Ranks.rankY]


theorem lamS_eq (R : Ranks) (P : HCParam R) (i : Fin R.r) : Formalism.MainNotions.S.lamS R P i = ((lamAt P i : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.S.lamS lamAt
  split_ifs <;> simp






variable {D : D7}

def frC (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (τ : D.what₂.Tau) : Matrix (Fin (D.sp.Y 0).rank) (Fin X.B.I.n) ℂ :=
  ((D.sp.Y 0).frame.toMatrix X.bas).map (tauE D τ)

def frC' (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (τ : D.what₂.Tau) : Matrix (Fin X.B.I.n) (Fin (D.sp.Y 0).rank) ℂ :=
  (X.bas.toMatrix (D.sp.Y 0).frame).map (tauE D τ)



theorem gram_change (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : NumberField.InfinitePlace X.B.I.F) :
    (frC X (X.pl v))ᴴ * gramAt D (D.sp.Y 0) (X.pl v) * frC X (X.pl v) = X.B.I.J.map (X.B.I.φ v) := by
  ext i j
  rw [Matrix.map_apply, X.φ_eq, X.J_eq]
  show _ = tauE D (X.pl v) ((D.sp.Y 0).hT (X.bas i) (X.bas j))
  rw [← (D.sp.Y 0).frame.sum_repr (X.bas i), ← (D.sp.Y 0).frame.sum_repr (X.bas j)]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, starRingEnd_apply, Eqv.tauE_star, Matrix.mul_apply, conjTranspose_apply, frC, gramAt,
    Matrix.map_apply, Module.Basis.toMatrix_apply, HSpace.gram]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable {S : D.what₂.Tau → SPar}

def Afr (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : DSModel (D.sp.Y 0) S) (v : NumberField.InfinitePlace X.B.I.F) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin X.B.I.n) ℂ :=
  M.fr (X.pl v) * frC X (X.pl v) * X.B.I.P v

def Afr' (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : DSModel (D.sp.Y 0) S) (v : NumberField.InfinitePlace X.B.I.F) :
    Matrix (Fin X.B.I.n) (Fin (D.sp.Y 0).rank) ℂ :=
  (X.B.I.P v)⁻¹ * frC' X (X.pl v) * (M.fr (X.pl v))⁻¹





end Formalism.IndefR.ModelConjugation
