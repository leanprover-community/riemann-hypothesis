import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataForm
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLoc
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective

section
noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section CC

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

def ccL (σ : Type) : MvPolynomial σ K →ₗ[K] K := lcoeff K 0


def ccInt (σ : Type) : Submodule R (MvPolynomial σ K) :=
  (LinearMap.range (Algebra.linearMap R K)).comap ((ccL K σ).restrictScalars R)

theorem mem_ccInt {σ : Type} (F : MvPolynomial σ K) : F ∈ ccInt R K σ ↔ ∃ a : R, algebraMap R K a = constantCoeff F :=
  Iff.rfl

theorem cc_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) K) (F : MvPolynomial (Fin r × Fin n) K) :
    constantCoeff (rowAct K g F) = constantCoeff F := by
  have : (constantCoeff.comp (rowAct K (n := n) g).toRingHom : MvPolynomial (Fin r × Fin n) K →+* K) = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [rowAct]
    · intro v; simp [rowAct]
  exact congrArg (fun f : MvPolynomial (Fin r × Fin n) K →+* K => f F) this

theorem nablaLTw_le_ccInt (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    nablaLTw R K m 0 g ≤ ccInt R K _ := by
  rintro F ⟨F', hF', rfl⟩
  obtain ⟨P, -, hP⟩ := hF'
  rw [mem_ccInt]
  refine ⟨constantCoeff P, ?_⟩
  have h1 : constantCoeff (rowAct K g F') = algebraMap R K (constantCoeff P) := by
    have hP' : mapAlgHom (Algebra.ofId R K) P = rowAct K g F' := hP
    rw [← hP', mapAlgHom_apply, constantCoeff_map]
    rfl
  rw [cc_rowAct] at h1
  simp [h1]




theorem const_of_dualWeyl (r n : ℕ) (F : MvPolynomial (Fin r × Fin n) K) (hF : F ∈ dualWeyl K r n 0) :
    F = C (constantCoeff F) := by
  have hw : IsWeightedHomogeneous (colW r n) F 0 := (mem_weightedHomogeneousSubmodule K (colW r n) 0 F).1 hF.1
  have : Finsupp.NonTorsionWeight ℕ (colW r n) :=
    ⟨fun {c v} h0 => by
      have := congrFun h0 v.2
      simpa [colW] using this⟩
  ext d
  by_cases hd : d = 0
  · subst hd; simp [constantCoeff_eq]
  · rw [coeff_C, if_neg (Ne.symm hd)]
    by_contra hc
    exact hd ((Finsupp.weight_eq_zero_iff_eq_zero (colW r n)).1 (hw hc))

theorem Vsp_le {n' m : ℕ} : Vsp K (fun _ _ => 0 : Fin n' → Fin (m + 1) → ℤ) ≤ Submodule.span K {1} := by
  unfold Vsp tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  have h1 : ∀ s, F s = C (constantCoeff (F s)) := fun s => by
    have h2 := hF s
    simp only [lamAt_zero] at h2
    rw [if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)] at h2
    have h0 : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by funext t; simp [nuOf]
    rw [h0] at h2
    exact const_of_dualWeyl K _ _ _ h2
  refine Submodule.mem_span_singleton.2 ⟨∏ s, constantCoeff (F s), ?_⟩
  have : ∀ s, blockEmb K s (F s) = C (constantCoeff (F s)) := fun s => by
    conv_lhs => rw [h1 s]
    simp [blockEmb]
  simp only [this]
  rw [smul_eq_C_mul, mul_one, map_prod]


theorem one_mem_Vsp {n' m : ℕ} : (1 : MvPolynomial _ K) ∈ Vsp K (fun _ _ => 0 : Fin n' → Fin (m + 1) → ℤ) := by
  unfold Vsp
  refine one_mem_tensorLat K K _ fun s => ?_
  rw [lamAt_zero, if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)]
  have h0 : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by funext t; simp [nuOf]
  rw [h0]
  exact one_mem_dualWeyl K _ _


end CC

end Formalism.MainNotions.G.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def gen (Qq : Type) [Field Qq] (p : ℕ) (a : ℤ) : Fin 1 → Qq := fun _ => (p : Qq) ^ a

theorem gen_mem (a : ℤ) : gen Qq p a ∈ line W (Qq := Qq) p a := Submodule.mem_span_singleton_self _




def toQuot (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) :
    W →ₗ[W] (↥(line W (Qq := Qq) p a) ⧸ Submodule.comap (line W (Qq := Qq) p a).subtype (line W p (a + 1))) :=
  (Submodule.mkQ _).comp (LinearMap.toSpanSingleton W _ ⟨gen Qq p a, Submodule.mem_span_singleton_self _⟩)




def edge1 (W : Type) (Qq : Type) [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) : Edge W Qq 1 :=
  ⟨line W p (a + 1), line W p a⟩



end Formalism.MainNotions.G.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

abbrev Z0 (n' : ℕ) : Fin n' → Fin (0 + 1) → ℤ := fun _ _ => 0


def oneV (Kf : Type) [Field Kf] (n' : ℕ) : Vsp Kf (Z0 n') := ⟨1, one_mem_Vsp Kf⟩

def evV (Kf : Type) [Field Kf] (n' : ℕ) : Module.Dual Kf (Vsp Kf (Z0 n')) := (ccL Kf _).comp (Vsp Kf (Z0 n')).subtype





theorem ext_lat (h : HidaSetting p n' W Qq O Kf ι σ j w) (L : Submodule W (Fin (0 + 1) → Qq)) (hL : IsLattice W L) (s : ℕ) :
    IsLattice O (extO O ι σ s L) :=
  LatticeSystems.je_extO_lat (gat1 h) (0 : Fin 1) s L hL







end Formalism.MainNotions.G.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section Const

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

theorem mem_span_one {σ : Type} (F : MvPolynomial σ K) :
    F ∈ Submodule.span R {(1 : MvPolynomial σ K)} ↔ ∃ a : R, F = C (algebraMap R K a) := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_apply]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_apply]⟩

theorem nuOf_zero (m : ℕ) : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by funext t; simp [nuOf]

theorem nablaLTw_le_const (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) :
    nablaLTw R K m 0 g ≤ Submodule.span R {1} := by
  intro F hF
  have h1 := LatticeSystems.la_nablaLTw_le m 0 g hg F hF
  rw [nuOf_zero] at h1
  have h2 := const_of_dualWeyl K _ _ F h1
  obtain ⟨a, ha⟩ := (mem_ccInt R K _).1 (nablaLTw_le_ccInt R K m g hF)
  exact (mem_span_one R K F).2 ⟨a, by rw [ha]; exact h2⟩

theorem applyWord_one (k : ℕ) (w : List (Fin k × Fin k × ℕ)) :
    ∃ a : R, applyWord R w (1 : MvPolynomial (Fin k × Fin k) R) = C a := by
  induction w with
  | nil => exact ⟨1, by simp [applyWord]⟩
  | cons x w ih =>
    obtain ⟨a, ha⟩ := ih
    have h1 : applyWord R (x :: w) (1 : MvPolynomial (Fin k × Fin k) R) =
        rowDiv R x.1 x.2.1 x.2.2 (applyWord R w 1) := rfl
    rw [h1, ha]
    unfold rowDiv
    have h2 : rowGen R x.1 x.2.1 (C a : MvPolynomial (Fin k × Fin k) R) = Polynomial.C (C a) := by
      have := (rowGen R (n := k) x.1 x.2.1).commutes a
      rw [MvPolynomial.algebraMap_eq] at this
      rw [this]
      rfl
    rw [h2, Polynomial.coeff_C]
    split_ifs
    · exact ⟨a, rfl⟩
    · exact ⟨0, by simp⟩

theorem weyl_zero_const (k : ℕ) (P : MvPolynomial (Fin k × Fin k) R) (hP : P ∈ weyl R k k le_rfl 0) :
    ∃ a : R, P = C a := by
  unfold weyl at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    have h1 : hw R (le_refl k) (0 : Fin k → ℕ) = 1 := by simp [hw]
    simp only [h1]
    exact applyWord_one R k w
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨c * a, by rw [smul_eq_C_mul, map_mul]⟩

theorem rowAct_one' (k n : ℕ) : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨a, s⟩
  simp only [rowAct, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rowAct_cancel (k n : ℕ) (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (F : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g⁻¹ (rowAct K g F) = F := by
  have h1 := rowActMul K k n g⁻¹ g
  rw [Matrix.mul_nonsing_inv g hg, rowAct_one'] at h1
  exact congrArg (fun f : MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (Fin k × Fin n) K => f F) h1

theorem deltaLTw_le_const (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) :
    deltaLTw R K m 0 g ≤ Submodule.span R {1} := by
  rintro F ⟨F', hF', rfl⟩
  obtain ⟨P, hP, hPF⟩ := hF'
  rw [nuOf_zero] at hP
  obtain ⟨a, rfl⟩ := weyl_zero_const R _ P hP
  have h1 : rowAct K g F' = C (algebraMap R K a) := by
    have : mapAlgHom (Algebra.ofId R K) (C a : MvPolynomial _ R) = rowAct K g F' := hPF
    rw [← this, mapAlgHom_apply, map_C]
    rfl
  have h2 : F' = C (algebraMap R K a) := by
    rw [← rowAct_cancel K _ _ g hg F', h1]
    simp [rowAct]
  refine (mem_span_one R K _).2 ⟨a, ?_⟩
  simp [h2]

theorem H0_degree_zero_le_constants (m : ℕ) (Λ : Submodule R (Fin (m + 1) → K)) (hΛ : IsLattice R Λ) :
    H0 R m 0 Λ ≤ Submodule.span R {1} := by
  obtain ⟨g, hg, rfl⟩ := hΛ
  exact (LatticeSystems.H0_le_twisted_nabla m 0 (fun _ _ _ => le_rfl) g hg).trans (nablaLTw_le_const R K m g hg)

theorem Dl0_le_const (m : ℕ) (Λ : Submodule R (Fin (m + 1) → K)) (hΛ : IsLattice R Λ) :
    Dl0 R m 0 Λ ≤ Submodule.span R {1} := by
  obtain ⟨g, hg, rfl⟩ := hΛ
  unfold Dl0
  rw [if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)]
  exact (iInf₂_le g ⟨hg, rfl⟩).trans (deltaLTw_le_const R K m g hg)

theorem tensorLat_le_const {S : Type} [Fintype S] {k n : ℕ} (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, M s ≤ Submodule.span R {1}) : tensorLat R K M ≤ Submodule.span R {1} := by
  unfold tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  choose a ha using fun s => (mem_span_one R K _).1 (h s (hF s))
  refine (mem_span_one R K _).2 ⟨∏ s, a s, ?_⟩
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [ha s, blockEmb, rename_C]

end Const

section Tup

variable {p : ℕ} (G : GAtP p) (h0 : ∀ v, G.P.lam0 v = fun _ _ => 0)

theorem tenV_le_const (M : ∀ v, Submodule G.O (MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf))
    (h : ∀ v, M v ≤ Submodule.span G.O {1}) : G.P.tenV M ≤ Submodule.span G.O {1} := by
  unfold Places.tenV
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  choose a ha using fun v => (mem_span_one G.O G.Kf _).1 (h v (hF v))
  refine (mem_span_one G.O G.Kf _).2 ⟨∏ v, a v, ?_⟩
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [ha v, Places.vEmb, rename_C]

include h0 in
theorem Htup_le_const (L : G.P.Tup) (hL : G.P.IsLatTup L) : G.P.Htup L ≤ Submodule.span G.O {1} := by
  refine tenV_le_const G _ fun v => ?_
  unfold Hten
  refine tensorLat_le_const G.O G.Kf _ fun s => ?_
  rw [h0 v, lamAt_zero]
  exact H0_degree_zero_le_constants G.O G.Kf _ _ (LatticeSystems.je_extO_lat G v s.val (L v) (hL v))

include h0 in
theorem HtupW_le_const (L : G.P.Tup) (hL : G.P.IsLatTup L) : G.P.HtupW L ≤ Submodule.span G.O {1} := by
  refine tenV_le_const G _ fun v => ?_
  unfold HtenW
  refine tensorLat_le_const G.O G.Kf _ fun s => ?_
  rw [h0 v, lamAt_zero]
  exact Dl0_le_const G.O G.Kf _ _ (LatticeSystems.je_extO_lat G v s.val (L v) (hL v))

end Tup

end Formalism.MainNotions.G.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf} (C : Level P)

theorem mem_funMod (Hv : P.Tup → Submodule O P.Xsp) (F : P.Tup → P.Xsp) :
    F ∈ C.funMod Hv ↔ (∀ L, P.IsLatTup L → F L ∈ Hv L) ∧ (∀ L, ¬ P.IsLatTup L → F L = 0) ∧
      ∀ γ L, F (C.smul γ L) = ((C.χ γ : Oˣ) : O) • C.actX γ (F L) := by
  unfold Level.funMod
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.proj_apply,
    and_assoc, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply,
    sub_eq_zero]

end Gen

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def tup0 (h : HidaSetting p n' W Qq O Kf ι σ j w) : (places1 h).Tup := fun _ => line W p 0




def oneG (h : HidaSetting p n' W Qq O Kf ι σ j w) : (gat1 h).Fn := fun _ => oneFn (places1 h)








end Formalism.MainNotions.G.Inhab

end
end
