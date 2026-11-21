import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ReflectionFixesNormal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModTop

section
noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable {D : Dat A n r}

theorem L_uni (H : D.Hyp) {w : Fin r → n → A} {s : Fin r → Fin r → A} (hw : ∀ a, IsW D (w a))
    (hs : ∀ a b, s a b + D.σA (s b a) + D.h (w a) (w b) = 0) : D.Uni (D.L w s) := by
  intro x y
  have hwp : ∀ a v, D.h (w a) (D.pW v) = D.h (w a) v := by
    intro a v
    conv_rhs => rw [show v = D.pU v + D.pW v by rw [pW_apply]; abel]
    rw [h_add_right, h_W_pU H (hw a), zero_add]
  have hL : ∀ v, D.L w s v = v + (∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) v • D.e a) := by
    intro v
    rw [L_apply, add_sub_assoc]
    simp only [hwp]
  have k1 : ∀ u v, D.h u (∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) v • D.e a) = ∑ b, D.h (D.e b) v * (D.h u (w b) + ∑ a, s a b * D.h u (D.e a)) -
      ∑ a, D.h (w a) v * D.h u (D.e a) := by
    intro u v
    simp only [h_sub_right, h_sum_right, h_smul_right, h_add_right]
  have k2 : ∀ v u, D.h (∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) v • D.e a) u = ∑ b, D.σA (D.h (D.e b) v) * (D.h (w b) u +
      ∑ a, D.σA (s a b) * D.h (D.e a) u) - ∑ a, D.σA (D.h (w a) v) * D.h (D.e a) u := by
    intro v u
    simp only [h_sub_left, h_sum_left, h_smul_left, h_add_left]
  have zwe : ∀ b a, D.h (w b) (D.e a) = 0 := fun b a => h_W_e H (hw b) a
  have zew : ∀ a b, D.h (D.e a) (w b) = 0 := fun a b => (hw b).1 a
  have k3 : D.h (∑ b, D.h (D.e b) x • (w b + ∑ a, s a b • D.e a) - ∑ a, D.h (w a) x • D.e a)
      (∑ b, D.h (D.e b) y • (w b + ∑ a, s a b • D.e a) - ∑ a, D.h (w a) y • D.e a) =
      ∑ b, D.σA (D.h (D.e b) x) * ∑ d, D.h (D.e d) y * D.h (w b) (w d) := by
    rw [k2]
    simp only [k1, zwe, zew, H.ee, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
  have sxw : ∀ b, D.h x (w b) = D.σA (D.h (w b) x) := fun b => h_symm H (w b) x
  have sxe : ∀ a, D.h x (D.e a) = D.σA (D.h (D.e a) x) := fun a => h_symm H (D.e a) x
  have sww : ∀ a, D.σA (D.σA (D.h (w a) x)) = D.h (w a) x := fun a => H.σσ _
  rw [hL x, hL y, h_add_left, h_add_right, h_add_right, k1, k2, k3]
  simp only [sxw, sxe]

  have E1 : ∑ b, D.h (D.e b) y * (D.σA (D.h (w b) x) + ∑ a, s a b * D.σA (D.h (D.e a) x)) =
      ∑ b, D.h (D.e b) y * D.σA (D.h (w b) x) +
        ∑ b, ∑ a, D.h (D.e b) y * (s a b * D.σA (D.h (D.e a) x)) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have E2 : ∑ b, D.σA (D.h (D.e b) x) * (D.h (w b) y + ∑ a, D.σA (s a b) * D.h (D.e a) y) =
      ∑ b, D.σA (D.h (D.e b) x) * D.h (w b) y +
        ∑ b, ∑ a, D.σA (D.h (D.e b) x) * (D.σA (s a b) * D.h (D.e a) y) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [E1, E2]
  have tableDegreeTwoSixteen : ∑ b, D.h (D.e b) y * D.σA (D.h (w b) x) =
      ∑ a, D.σA (D.h (w a) x) * D.h (D.e a) y :=
    Finset.sum_congr rfl fun b _ => mul_comm _ _
  have A34 : ∑ a, D.h (w a) y * D.σA (D.h (D.e a) x) =
      ∑ b, D.σA (D.h (D.e b) x) * D.h (w b) y :=
    Finset.sum_congr rfl fun b _ => mul_comm _ _
  have A257 : ∑ b, ∑ a, D.h (D.e b) y * (s a b * D.σA (D.h (D.e a) x)) +
      ∑ b, ∑ a, D.σA (D.h (D.e b) x) * (D.σA (s a b) * D.h (D.e a) y) +
      ∑ b, D.σA (D.h (D.e b) x) * ∑ d, D.h (D.e d) y * D.h (w b) (w d) = 0 := by
    rw [Finset.sum_comm (f := fun b a => D.h (D.e b) y * (s a b * D.σA (D.h (D.e a) x)))]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    have := hs a b
    linear_combination (D.σA (D.h (D.e a) x) * D.h (D.e b) y) * this
  linear_combination tableDegreeTwoSixteen - A34 + A257

end Dat

end PI.VolSemiDirect.W.PG
end
end

section
noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable {D : Dat A n r}

theorem h_e_L (H : D.Hyp) {w' : Fin r → n → A} (s' : Fin r → Fin r → A)
    (hw' : ∀ a, IsW D (w' a)) (v : n → A) (c : Fin r) :
    D.h (D.e c) (D.L w' s' v) = D.h (D.e c) v := by
  rw [L_apply, h_sub_right, h_add_right, h_sum_right, h_sum_right]
  simp only [h_smul_right, h_add_right, h_sum_right, H.ee, (hw' _).1, mul_zero, add_zero,
    Finset.sum_const_zero, sub_zero]

theorem pW_L (H : D.Hyp) {w' : Fin r → n → A} (s' : Fin r → Fin r → A)
    (hw' : ∀ a, IsW D (w' a)) (v : n → A) :
    D.pW (D.L w' s' v) = D.pW v + ∑ d, D.h (D.e d) v • w' d := by
  rw [L_apply, map_sub, map_add, map_sum, map_sum]
  simp only [map_smul, map_add, map_sum, pW_e H, pW_of_isW (hw' _), smul_zero,
    Finset.sum_const_zero, add_zero, sub_zero]

theorem L_comp (H : D.Hyp) {w w' : Fin r → n → A} (s s' : Fin r → Fin r → A)
    (hw : ∀ a, IsW D (w a)) (hw' : ∀ a, IsW D (w' a)) (v : n → A) :
    D.L w s (D.L w' s' v) =
      D.L (w + w') (fun a b => s a b + s' a b - D.h (w a) (w' b)) v := by
  have _hw := hw
  have h1 : ∀ c, D.h (D.e c) (D.L w' s' v) = D.h (D.e c) v := h_e_L H s' hw' v
  have h3 : ∀ a, D.h (w a) (D.pW (D.L w' s' v)) =
      D.h (w a) (D.pW v) + ∑ d, D.h (D.e d) v * D.h (w a) (w' d) := fun a => by
    rw [pW_L H s' hw', h_add_right, h_sum_right]
    simp only [h_smul_right]
  have hZ : ∑ b, D.h (D.e b) v • ∑ a, D.h (w a) (w' b) • D.e a =
      ∑ a, (∑ d, D.h (D.e d) v * D.h (w a) (w' d)) • D.e a := by
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hB : ∀ b, D.h (D.e b) v • ((w + w') b +
        ∑ a, (s a b + s' a b - D.h (w a) (w' b)) • D.e a) =
      D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) + D.h (D.e b) v • (w' b + ∑ a, s' a b • D.e a) -
        D.h (D.e b) v • ∑ a, D.h (w a) (w' b) • D.e a := fun b => by
    simp only [Pi.add_apply, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      smul_add, smul_sub]
    abel
  have hA : ∀ a, D.h ((w + w') a) (D.pW v) • D.e a =
      D.h (w a) (D.pW v) • D.e a + D.h (w' a) (D.pW v) • D.e a := fun a => by
    rw [Pi.add_apply, h_add_left, add_smul]
  rw [L_apply D w s, L_apply D (w + w')]
  simp only [h1, h3, add_smul, Finset.sum_add_distrib]
  rw [L_apply D w' s']
  simp only [hB, hA, Finset.sum_add_distrib, Finset.sum_sub_distrib, hZ]
  abel

theorem L_zero : D.L 0 0 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [L_apply]
  simp [h_zero_left]

end Dat

end PI.VolSemiDirect.W.PG
end
end

section
noncomputable section

namespace PI.VolSemiDirect.W.PG.Dat

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {D : Dat A n r}

theorem S_L (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hf : ∀ a, S (D.f a) = D.f a)
    (hU : D.Uni S) (w : Fin r → n → A) (s : Fin r → Fin r → A) (u : n → A) :
    S (D.L w s u) = D.L (fun a => S (w a)) s (S u) := by
  rw [L_apply, L_apply, pW_comm H hS hf hU]
  have hw : ∀ a, D.h (S (w a)) (S (D.pW u)) = D.h (w a) (D.pW u) := fun a => hU _ _
  simp only [map_sub, map_add, map_sum, map_smul, hS.1, h_e_S hS hU, hw]

theorem h_neg_left' (x y : n → A) : D.h (-x) y = -D.h x y := by
  have := D.h_add_left (-x) x y
  rw [neg_add_cancel, h_zero_left] at this
  linear_combination -this

theorem h_neg_right' (x y : n → A) : D.h x (-y) = -D.h x y := by
  have := D.h_add_right x (-y) y
  rw [neg_add_cancel, h_zero_right] at this
  linear_combination -this

end PI.VolSemiDirect.W.PG.Dat

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField
open scoped TensorProduct

def half (F E R : Type) [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] : R ⊗[F] E :=
  inclR (F := F) R (1 / 2 : E)

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem half_add_half (h2 : (2 : E) ≠ 0) : half F E R + half F E R = 1 := by
  have : (1 / 2 : E) + 1 / 2 = 1 := by rw [← two_mul, mul_one_div_cancel h2]
  rw [half, ← map_add, this, map_one]

theorem sigR_half : sigR R σ (half F E R) = half F E R := by
  rw [half, sigR_inclR, map_div₀, map_one, map_ofNat]

variable (σ J) in

def Lr (P : Frame E M r) (T : F) (w : Fin r → Fin M → R ⊗[F] E) (c : Fin r → Fin r → R ⊗[F] E) :
    (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin M → R ⊗[F] E) :=
  (datR R σ J P T).L w (fun a b => c a b - half F E R * hR R σ J (w a) (w b))

variable (R σ J) in

def dat0 : PG.Dat (R ⊗[F] E) (Fin M) 0 where
  σA := sigR R σ
  JA := JR R J
  e := fun _ => 0
  f := fun _ => 0
  z := 0
  tz := 0

theorem hR_add_left' (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y :=
  PG.Dat.h_add_left (D := dat0 R σ J) x x' y

theorem hR_add_right' (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' :=
  PG.Dat.h_add_right (dat0 R σ J) x y y'

theorem hR_neg_left' (x y : Fin M → R ⊗[F] E) : hR R σ J (-x) y = -hR R σ J x y :=
  PG.Dat.h_neg_left' (D := dat0 R σ J) x y

theorem hR_neg_right' (x y : Fin M → R ⊗[F] E) : hR R σ J x (-y) = -hR R σ J x y :=
  PG.Dat.h_neg_right' (D := dat0 R σ J) x y

theorem Lr_zero : Lr σ J P T (0 : Fin r → Fin M → R ⊗[F] E) 0 = LinearMap.id := by
  have e : (fun a b => (0 : Fin r → Fin r → R ⊗[F] E) a b -
      half F E R * hR R σ J ((0 : Fin r → Fin M → R ⊗[F] E) a) ((0 : Fin r → Fin M → R ⊗[F] E) b)) =
      (0 : Fin r → Fin r → R ⊗[F] E) := by
    funext a b
    simp [hR_zero_left]
  rw [Lr, e]
  exact PG.Dat.L_zero

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (h2 : (2 : E) ≠ 0)
include hσσ hJ hP h2

theorem Lr_comp {w w' : Fin r → Fin M → R ⊗[F] E} (hw : ∀ a, w a ∈ Wsub R σ J P)
    (hw' : ∀ a, w' a ∈ Wsub R σ J P) (c c' : Fin r → Fin r → R ⊗[F] E) (v : Fin M → R ⊗[F] E) :
    Lr σ J P T w c (Lr σ J P T w' c' v) = Lr σ J P T (w + w') (c + c' + betaM R σ J w w') v := by
  have H := datR_hyp (R := R) hσσ hJ hP
  rw [Lr, Lr, PG.Dat.L_comp H _ _ (fun a => hw a) (fun a => hw' a), Lr]
  congr 2
  funext a b
  simp only [datR_h, Pi.add_apply, betaM]
  rw [hR_add_left', hR_add_right', hR_add_right']
  have hh := half_add_half (F := F) (R := R) h2
  rw [show inclR (F := F) R (1 / 2 : E) = half F E R from rfl]
  linear_combination (hR R σ J (w a) (w' b)) * hh

theorem Lr_inv {w : Fin r → Fin M → R ⊗[F] E} (hw : ∀ a, w a ∈ Wsub R σ J P)
    (c : Fin r → Fin r → R ⊗[F] E) :
    Lr σ J P T w c ∘ₗ Lr σ J P T (-w) (-c) = LinearMap.id ∧
      Lr σ J P T (-w) (-c) ∘ₗ Lr σ J P T w c = LinearMap.id := by
  have hwn : ∀ a, (-w) a ∈ Wsub R σ J P := fun a => (Wsub R σ J P).neg_mem (hw a)
  have b1 : c + -c + betaM R σ J w (-w) = 0 := by
    funext a b
    simp only [betaM, Pi.add_apply, Pi.neg_apply, Pi.zero_apply, hR_neg_left' ,
      hR_neg_right' ]
    ring
  have b2 : -c + c + betaM R σ J (-w) w = 0 := by
    funext a b
    simp only [betaM, Pi.add_apply, Pi.neg_apply, Pi.zero_apply, hR_neg_left' ,
      hR_neg_right' ]
    ring
  constructor
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, Lr_comp hσσ hJ hP h2 hw hwn, b1, add_neg_cancel, Lr_zero]
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, Lr_comp hσσ hJ hP h2 hwn hw, b2, neg_add_cancel, Lr_zero]

theorem Lr_uni {w : Fin r → Fin M → R ⊗[F] E} (hw : ∀ a, w a ∈ Wsub R σ J P)
    {c : Fin r → Fin r → R ⊗[F] E} (hc : ∀ a b, c a b + sigR R σ (c b a) = 0) :
    (datR R σ J P T).Uni (Lr σ J P T w c) := by
  have H := datR_hyp (R := R) hσσ hJ hP
  refine PG.Dat.L_uni H (fun a => hw a) fun a b => ?_
  have hsym : hR R σ J (w a) (w b) = sigR R σ (hR R σ J (w b) (w a)) :=
    PG.Dat.h_symm H (w b) (w a)
  have hh := half_add_half (F := F) (R := R) h2
  show c a b - half F E R * hR R σ J (w a) (w b) +
      sigR R σ (c b a - half F E R * hR R σ J (w b) (w a)) + hR R σ J (w a) (w b) = 0
  rw [map_sub, map_mul, sigR_half, ← hsym]
  linear_combination hc a b - hR R σ J (w a) (w b) * hh

def wv (w : Fin r → Wsub R σ J P) : Fin r → Fin M → R ⊗[F] E := fun a => (w a : Fin M → R ⊗[F] E)

def nU (w : Fin r → Wsub R σ J P) (c : Sk R σ r) : GL (Fin M) (R ⊗[F] E) where
  val := LinearMap.toMatrix' (Lr σ J P T (wv w) c)
  inv := LinearMap.toMatrix' (Lr σ J P T (-wv w) (-(c : Fin r → Fin r → R ⊗[F] E)))
  val_inv := by
    rw [← LinearMap.toMatrix'_comp, (Lr_inv hσσ hJ hP h2 (w := wv w) (fun a => (w a).2) _).1,
      LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp, (Lr_inv hσσ hJ hP h2 (w := wv w) (fun a => (w a).2) _).2,
      LinearMap.toMatrix'_id]

theorem nU_mem (w : Fin r → Wsub R σ J P) (c : Sk R σ r) : nU hσσ hJ hP h2 w c ∈ HR R σ J := by
  show Formalism.UG.cT (sigR R σ) (LinearMap.toMatrix' (Lr σ J P T (wv w) c)) * JR R J *
    LinearMap.toMatrix' (Lr σ J P T (wv w) c) = JR R J
  apply uj_of_uni
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  exact Lr_uni hσσ hJ hP h2 (fun a => (w a).2) (fun a b => c.2 a b) x y

def nG (w : Fin r → Wsub R σ J P) (c : Sk R σ r) : HA R σ J :=
  ⟨nU hσσ hJ hP h2 w c, nU_mem hσσ hJ hP h2 w c⟩

theorem lin_nG (w : Fin r → Wsub R σ J P) (c : Sk R σ r) :
    lin R σ J (nG hσσ hJ hP h2 w c) = Lr σ J P T (wv w) c :=
  LinearMap.ext fun v => LinearMap.toMatrix'_mulVec _ v

theorem nG_mem (w : Fin r → Wsub R σ J P) (c : Sk R σ r) :
    nG hσσ hJ hP h2 w c ∈ FrameUnipotentSubgroup R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have he : ∀ b, lin R σ J (nG hσσ hJ hP h2 w c) (ratV (F := F) R (P.e b)) =
      ratV (F := F) R (P.e b) := fun b => by
    rw [lin_nG]; exact PG.Dat.L_e H _ _ b
  have hz : lin R σ J (nG hσσ hJ hP h2 w c) (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
    rw [lin_nG]; exact PG.Dat.reflection_fixes_normal H _ _
  rw [FrameUnipotentSubgroup, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · show UniC R σ J P.e _ ∧ ∀ v, InXperp R σ J P v → _
    refine ⟨fun b => ?_, fun v hv => ?_⟩
    · rw [he b, sub_self]
      exact Submodule.zero_mem _
    · rw [spanR_eq hσσ hJ hP, lin_nG]
      exact PG.Dat.L_perp H _ _ v hv
  · rw [S0, mem_stabT]
    intro b
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simp only [F0, Fin.snoc_last]; exact hz
    · simp only [F0, Fin.snoc_castSucc]; exact he a

omit h2 in
theorem phiW_mem (n : FrameUnipotentSubgroup R σ J P) (b : Fin r) :
    (datR R σ J P T).pW (lin R σ J n ((datR R σ J P T).f b)) ∈ Wsub R σ J P :=
  PG.Dat.isW_pW (datR_hyp hσσ hJ hP) _

omit h2 in

def phiW (n : FrameUnipotentSubgroup R σ J P) : Fin r → Wsub R σ J P := fun b =>
  ⟨(datR R σ J P T).pW (lin R σ J n ((datR R σ J P T).f b)), phiW_mem hσσ hJ hP n b⟩

omit h2 in

def phiSv (n : FrameUnipotentSubgroup R σ J P) : Fin r → Fin r → R ⊗[F] E := fun a b =>
  hR R σ J ((datR R σ J P T).f a) (lin R σ J n ((datR R σ J P T).f b)) +
    half F E R * hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b)

theorem phiSv_mem (n : FrameUnipotentSubgroup R σ J P) : phiSv hσσ hJ hP n ∈ Sk R σ r := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have hS0 : (n : HA R σ J) ∈ S0 R σ J P := (Subgroup.mem_inf.1 n.2).2
  have hN := PG.Dat.N_skew H (stabilizer_fixes_frame_and_normal (T := T) hS0) (uni_lin (T := T) (n : HA R σ J))
  have hh := half_add_half (F := F) (R := R) h2
  intro a b
  have hsym : hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b) =
      sigR R σ (hR R σ J (wv (phiW hσσ hJ hP n) b) (wv (phiW hσσ hJ hP n) a)) :=
    PG.Dat.h_symm H _ _
  show phiSv hσσ hJ hP n a b + sigR R σ (phiSv hσσ hJ hP n b a) = 0
  simp only [phiSv]
  rw [map_add, map_mul, sigR_half, ← hsym]
  have k := hN a b
  simp only [datR_h] at k
  change hR R σ J ((datR R σ J P T).f a) (lin R σ J n ((datR R σ J P T).f b)) +
    sigR R σ (hR R σ J ((datR R σ J P T).f b) (lin R σ J n ((datR R σ J P T).f a))) +
    hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b) = 0 at k
  linear_combination k + hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b) * hh

def phiS (n : FrameUnipotentSubgroup R σ J P) : Sk R σ r := ⟨phiSv hσσ hJ hP n, phiSv_mem hσσ hJ hP h2 n⟩

omit h2 in

theorem phi_of_lin (n : FrameUnipotentSubgroup R σ J P) {w : Fin r → Fin M → R ⊗[F] E} (hw : ∀ a, w a ∈ Wsub R σ J P)
    (c : Fin r → Fin r → R ⊗[F] E) (hn : lin R σ J n = Lr σ J P T w c) :
    wv (phiW hσσ hJ hP n) = w ∧ phiSv hσσ hJ hP n = c := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have h1 : wv (phiW hσσ hJ hP n) = w := by
    funext b
    show (datR R σ J P T).pW (lin R σ J n ((datR R σ J P T).f b)) = w b
    rw [hn, Lr]
    exact PG.Dat.coordW_L H (fun a => hw a) _ b
  refine ⟨h1, ?_⟩
  funext a b
  simp only [phiSv]
  rw [h1, hn, Lr]
  have := PG.Dat.coordS_L H (fun a => hw a)
    (fun a b => c a b - half F E R * hR R σ J (w a) (w b)) a b
  rw [datR_h] at this
  rw [this]
  ring

omit h2 in
theorem lin_eq_Lr (n : FrameUnipotentSubgroup R σ J P) :
    lin R σ J n = Lr σ J P T (wv (phiW hσσ hJ hP n)) (phiSv hσσ hJ hP n) := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have hS0 : (n : HA R σ J) ∈ S0 R σ J P := (Subgroup.mem_inf.1 n.2).2
  have hNs := (Subgroup.mem_inf.1 n.2).1
  have hperp : (datR R σ J P T).PerpX (lin R σ J n) := fun v hv => by
    have := hNs.2 v hv
    rwa [spanR_eq hσσ hJ hP] at this
  have hs : (fun a b => phiSv hσσ hJ hP n a b - half F E R *
      hR R σ J (wv (phiW hσσ hJ hP n) a) (wv (phiW hσσ hJ hP n) b)) =
      fun a b => (datR R σ J P T).h ((datR R σ J P T).f a) (lin R σ J n ((datR R σ J P T).f b)) := by
    funext a b
    simp only [phiSv]
    rw [add_sub_cancel_right]
    rfl
  refine LinearMap.ext fun v => ?_
  rw [Lr, hs]
  exact PG.Dat.N_eq_L H (stabilizer_fixes_frame_and_normal hS0) (uni_lin _) hperp v

theorem nG_phi (n : FrameUnipotentSubgroup R σ J P) :
    nG hσσ hJ hP h2 (phiW hσσ hJ hP n) (phiS hσσ hJ hP h2 n) = n := by
  have e : lin R σ J (nG hσσ hJ hP h2 (phiW hσσ hJ hP n) (phiS hσσ hJ hP h2 n)) = lin R σ J n :=
    (lin_nG hσσ hJ hP h2 _ _).trans (lin_eq_Lr hσσ hJ hP n).symm
  apply HA_ext
  rw [← lin_eq_toLin', ← lin_eq_toLin', e]

theorem phi_nG (w : Fin r → Wsub R σ J P) (c : Sk R σ r) :
    phiW hσσ hJ hP ⟨nG hσσ hJ hP h2 w c, nG_mem hσσ hJ hP h2 w c⟩ = w ∧
      phiS hσσ hJ hP h2 ⟨nG hσσ hJ hP h2 w c, nG_mem hσσ hJ hP h2 w c⟩ = c := by
  obtain ⟨h1, h2'⟩ := phi_of_lin hσσ hJ hP ⟨nG hσσ hJ hP h2 w c, nG_mem hσσ hJ hP h2 w c⟩
    (fun a => (w a).2) c (lin_nG hσσ hJ hP h2 w c)
  exact ⟨funext fun b => Subtype.ext (congrFun h1 b), Subtype.ext h2'⟩

def coordEquiv : FrameUnipotentSubgroup R σ J P ≃ ((Fin r → Wsub R σ J P) × Sk R σ r) where
  toFun n := (phiW hσσ hJ hP n, phiS hσσ hJ hP h2 n)
  invFun p := ⟨nG hσσ hJ hP h2 p.1 p.2, nG_mem hσσ hJ hP h2 p.1 p.2⟩
  left_inv n := Subtype.ext (nG_phi hσσ hJ hP h2 n)
  right_inv p := Prod.ext (phi_nG hσσ hJ hP h2 p.1 p.2).1 (phi_nG hσσ hJ hP h2 p.1 p.2).2

theorem phi_mul (n₀ n : FrameUnipotentSubgroup R σ J P) :
    wv (phiW hσσ hJ hP (n₀ * n)) = wv (phiW hσσ hJ hP n₀) + wv (phiW hσσ hJ hP n) ∧
      phiSv hσσ hJ hP (n₀ * n) = phiSv hσσ hJ hP n₀ + phiSv hσσ hJ hP n +
        betaM R σ J (wv (phiW hσσ hJ hP n₀)) (wv (phiW hσσ hJ hP n)) := by
  have hl : lin R σ J ((n₀ * n : FrameUnipotentSubgroup R σ J P) : HA R σ J) =
      Lr σ J P T (wv (phiW hσσ hJ hP n₀) + wv (phiW hσσ hJ hP n))
        (phiSv hσσ hJ hP n₀ + phiSv hσσ hJ hP n +
          betaM R σ J (wv (phiW hσσ hJ hP n₀)) (wv (phiW hσσ hJ hP n))) := by
    refine LinearMap.ext fun v => ?_
    rw [Subgroup.coe_mul, lin_mul, lin_eq_Lr hσσ hJ hP n₀, lin_eq_Lr hσσ hJ hP n,
      Lr_comp hσσ hJ hP h2 (w := wv (phiW hσσ hJ hP n₀)) (w' := wv (phiW hσσ hJ hP n))
      (fun a => (phiW hσσ hJ hP n₀ a).2) (fun a => (phiW hσσ hJ hP n a).2)]
  exact phi_of_lin hσσ hJ hP (n₀ * n)
    (fun a => (Wsub R σ J P).add_mem (phiW hσσ hJ hP n₀ a).2 (phiW hσσ hJ hP n a).2) _ hl

theorem phi_conj {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (n n' : FrameUnipotentSubgroup R σ J P)
    (hn : (n' : HA R σ J) = h * n * h⁻¹) :
    wv (phiW hσσ hJ hP n') = (fun a => lin R σ J h (wv (phiW hσσ hJ hP n) a)) ∧
      phiSv hσσ hJ hP n' = phiSv hσσ hJ hP n := by
  have H := datR_hyp (R := R) hσσ hJ hP
  have hS := stabilizer_fixes_frame_and_normal (T := T) (heisenberg_le_stabilizer R σ J P hh)
  have hf : ∀ b, lin R σ J h ((datR R σ J P T).f b) = (datR R σ J P T).f b :=
    fun b => fix_f_of_H hσσ hJ hP hh b
  have hU := uni_lin (T := T) (P := P) h
  have hw : ∀ a, lin R σ J h (wv (phiW hσσ hJ hP n) a) ∈ Wsub R σ J P :=
    fun a => lin_mem_Wsub hh (phiW hσσ hJ hP n a).2
  have hl : lin R σ J (n' : HA R σ J) =
      Lr σ J P T (fun a => lin R σ J h (wv (phiW hσσ hJ hP n) a)) (phiSv hσσ hJ hP n) := by
    refine LinearMap.ext fun v => ?_
    rw [hn, lin_mul, lin_mul, lin_eq_Lr hσσ hJ hP n, Lr, PG.Dat.S_L H hS hf hU, lin_lin_inv, Lr]
    congr 2
    funext a b
    rw [hR_lin]
  exact phi_of_lin hσσ hJ hP n' hw _ hl

end R

end PI.VolSemiDirect.W.Md
end
end

section
noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section Homeo

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (h2 : (2 : E) ≠ 0)

theorem continuous_wv_phiW :
    Continuous fun n : FrameUnipotentSubgroup R σ J P => wv (phiW hσσ hJ hP n) :=
  continuous_phiW_raw R σ J P T

theorem continuous_phiW : Continuous fun n : FrameUnipotentSubgroup R σ J P => phiW hσσ hJ hP n :=
  continuous_pi fun b => continuous_induced_rng.2
    ((continuous_apply b).comp (continuous_wv_phiW hσσ hJ hP))

theorem continuous_phiSv : Continuous fun n : FrameUnipotentSubgroup R σ J P => phiSv hσσ hJ hP n :=
  continuous_gram_add R σ J (half F E R) (continuous_wv_phiW hσσ hJ hP)
    (continuous_phiS_raw R σ J P)

theorem continuous_phiS : Continuous fun n : FrameUnipotentSubgroup R σ J P => phiS hσσ hJ hP h2 n :=
  continuous_induced_rng.2 (continuous_phiSv hσσ hJ hP)

theorem continuous_nG :
    Continuous fun p : (Fin r → Wsub R σ J P) × Sk R σ r => nG hσσ hJ hP h2 p.1 p.2 := by
  apply continuous_into_HA hJ
  have hw : Continuous fun p : (Fin r → Wsub R σ J P) × Sk R σ r => wv p.1 :=
    continuous_pi fun a => continuous_subtype_val.comp ((continuous_apply a).comp continuous_fst)
  have hc : Continuous fun p : (Fin r → Wsub R σ J P) × Sk R σ r =>
      (p.2 : Fin r → Fin r → R ⊗[F] E) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_toMatrix'_L R σ J P T hw (continuous_gram_shift R σ J (half F E R) hw hc)

def coordHomeo : FrameUnipotentSubgroup R σ J P ≃ₜ ((Fin r → Wsub R σ J P) × Sk R σ r) where
  toEquiv := coordEquiv hσσ hJ hP h2
  continuous_toFun :=
    (continuous_phiW hσσ hJ hP).prodMk (continuous_phiS hσσ hJ hP h2)
  continuous_invFun := continuous_induced_rng.2 (continuous_nG hσσ hJ hP h2)

end Homeo

end PI.VolSemiDirect.W.Md
end
end

section
noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField


end PI.VolSemiDirect.W.Md
end
end
