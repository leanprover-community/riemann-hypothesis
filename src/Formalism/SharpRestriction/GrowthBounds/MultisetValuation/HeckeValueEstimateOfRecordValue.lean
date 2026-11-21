import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremCIiiMulti

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem edges_fin (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L⟩}.Finite := by
  apply Formalism.MainNotions.G.LatticeSystems.ef_edges_finite_gen
  apply Nat.finite_of_card_ne_zero
  rw [(P.setting v).res_card]
  exact pow_ne_zero _ (P.setting v).prime.ne_zero

def EE (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (edges_fin P v i L).toFinset

theorem mem_EE {v : Fin P.nV} {i : ℕ} {L L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    L'' ∈ EE P v i L ↔ IsEdge p (P.n' v) i ⟨L'', L⟩ :=
  Set.Finite.mem_toFinset _

theorem Tminus_eq (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) :
    P.Tminus v i F L = ∑ L'' ∈ EE P v i (L v), F (Function.update L v L'') :=
  finsum_mem_eq_finite_toFinset_sum _ (edges_fin P v i (L v))

def TminusLin (v : Fin P.nV) (i : ℕ) : (P.Tup → P.Xsp) →ₗ[Kf] (P.Tup → P.Xsp) where
  toFun := P.Tminus v i
  map_add' F F' := by
    funext L
    rw [Pi.add_apply, Tminus_eq, Tminus_eq, Tminus_eq, ← Finset.sum_add_distrib]
    rfl
  map_smul' c F := by
    funext L
    rw [RingHom.id_apply, Pi.smul_apply, Tminus_eq, Tminus_eq, Finset.smul_sum]
    rfl

@[simp] theorem TminusLin_apply (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) :
    TminusLin P v i F = P.Tminus v i F := rfl

theorem edge_zero_iff {v : Fin P.nV} {L L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    IsEdge p (P.n' v) 0 ⟨L'', L⟩ ↔ IsLattice (P.W v) L ∧ L'' = L := by
  constructor
  · rintro ⟨_, h2, h3, _, h5⟩
    refine ⟨h2, le_antisymm h3 ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_unique] at h5
    have h6 := (Submodule.Quotient.subsingleton_iff).1 h5.1
    intro x hx
    have : (⟨x, hx⟩ : L) ∈ Submodule.comap L.subtype L'' := by
      have h7 : Submodule.comap L.subtype L'' = ⊤ := h6
      rw [h7]
      exact Submodule.mem_top
    exact this
  · rintro ⟨h, rfl⟩
    refine ⟨h, h, le_rfl, fun x hx => Submodule.smul_mem _ _ hx, ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_unique]
    have h7 : Submodule.comap (L''.subtype) L'' = ⊤ := Submodule.comap_subtype_self L''
    refine ⟨(Submodule.Quotient.subsingleton_iff).2 h7, ⟨0⟩⟩

theorem Tminus_zero_lat (v : Fin P.nV) (F : P.Tup → P.Xsp) (L : P.Tup) (hL : IsLattice (P.W v) (L v)) :
    P.Tminus v 0 F L = F L := by
  rw [Tminus_eq]
  have : EE P v 0 (L v) = {L v} := by
    ext A
    rw [mem_EE, edge_zero_iff, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨hL, h⟩⟩
  rw [this, Finset.sum_singleton]
  exact congrArg F (Function.update_eq_self v L)

theorem Tminus_not_lat (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) (hL : ¬ IsLattice (P.W v) (L v)) :
    P.Tminus v i F L = 0 := by
  rw [Tminus_eq]
  have : EE P v i (L v) = ∅ := by
    ext A
    rw [mem_EE]
    simp only [Finset.notMem_empty, iff_false]
    exact fun h => hL h.2.1
  rw [this, Finset.sum_empty]

end PlacesLevel

section SysLevel

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def TmLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j where
  toFun := X.Tm v i j
  map_add' F F' := by
    funext c
    exact (TminusLin (X.Pj j) (X.vJ j v) i).map_add (F c) (F' c)
  map_smul' a F := by
    funext c
    exact (TminusLin (X.Pj j) (X.vJ j v) i).map_smul a (F c)

@[simp] theorem TmLin_apply (v : X.Pl) (i j : ℕ) (F : X.Fm j) : TmLin X v i j F = X.Tm v i j F := rfl

def TtLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  if i = 0 then LinearMap.id else ((p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) j i)) • TmLin X v i j

@[simp] theorem TtLin_apply (v : X.Pl) (i j : ℕ) (F : X.Fm j) : TtLin X v i j F = X.Tt v i j F := by
  unfold TtLin Sys.Tt
  split_ifs <;> rfl

def TtuLin (v : X.Pl) (u : ℕ → X.G.Kf) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  ((∏ l ∈ Icc 1 j, u l) ^ (-(i : ℤ))) • TtLin X v i j

@[simp] theorem TtuLin_apply (v : X.Pl) (u : ℕ → X.G.Kf) (i j : ℕ) (F : X.Fm j) :
    TtuLin X v u i j F = X.Ttu v u i j F := by
  unfold TtuLin Sys.Ttu
  rw [LinearMap.smul_apply, TtLin_apply]

def ZopLin (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  ∑ l ∈ range (X.G.P.r + 1), ((-1 : X.G.Kf) ^ l * X.cl v m j l) • TtuLin X v u (X.G.P.r - l) j

@[simp] theorem ZopLin_apply (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) (F : X.Fm j) :
    ZopLin X v u m j F = X.Zop v u m j F := by
  unfold ZopLin Sys.Zop
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.smul_apply, TtuLin_apply]

def ecalLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  ((p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * i * ((NN X.G.P.m X.t j : ℤ) - i)))) • TmLin X v i j

@[simp] theorem ecalLin_apply (v : X.Pl) (i j : ℕ) (F : X.Fm j) : ecalLin X v i j F = X.ecal v i j F := rfl

theorem yv_eq (v : X.Pl) (F : X.Fm 0) : X.yv v F = ((p : X.G.Kf) ^ X.G.P.ArV v) • X.Tm v X.G.P.r 0 F := rfl

def yvLin (v : X.Pl) : X.Fm 0 →ₗ[X.G.Kf] X.Fm 0 := ((p : X.G.Kf) ^ X.G.P.ArV v) • TmLin X v X.G.P.r 0

@[simp] theorem yvLin_apply (v : X.Pl) (F : X.Fm 0) : yvLin X v F = X.yv v F := rfl

theorem Int_zero_off {j : ℕ} {F : X.Fm j} (hF : F ∈ X.Int j) (c : X.Lv.comp j) (L : (X.Pj j).Tup)
    (hL : ¬ (X.Pj j).IsLatTup L) : F c L = 0 := by
  have h1 : F c ∈ (X.Lv.lev j c).M := hF c (Set.mem_univ c)
  unfold Level.M Level.funMod at h1
  have h2 : F c ∈ (⨅ (L : (X.Pj j).Tup) (_ : ¬ (X.Pj j).IsLatTup L),
      LinearMap.ker (LinearMap.proj (R := X.G.O) (φ := fun _ : (X.Pj j).Tup => (X.Pj j).Xsp) L)) := h1.1.2
  rw [Submodule.mem_iInf] at h2
  have h3 := h2 L
  rw [Submodule.mem_iInf] at h3
  exact h3 hL

theorem FQ_zero_off {j : ℕ} {F : X.Fm j} (hF : F ∈ X.FQ j) (c : X.Lv.comp j) (L : (X.Pj j).Tup)
    (hL : ¬ (X.Pj j).IsLatTup L) : F c L = 0 := by
  unfold Sys.FQ at hF
  induction hF using Submodule.span_induction with
  | mem x hx => exact Int_zero_off X hx c L hL
  | zero => rfl
  | add x y _ _ hx hy => rw [Pi.add_apply, Pi.add_apply, hx, hy, add_zero]
  | smul a x _ hx => rw [Pi.smul_apply, Pi.smul_apply, hx, smul_zero]

theorem Tm_zero {j : ℕ} (v : X.Pl) {F : X.Fm j} (hF : F ∈ X.FQ j) : X.Tm v 0 j F = F := by
  funext c L
  show (X.Pj j).Tminus (X.vJ j v) 0 (F c) L = F c L
  by_cases hL : IsLattice ((X.Pj j).W (X.vJ j v)) (L (X.vJ j v))
  · exact Tminus_zero_lat _ _ _ _ hL
  · rw [Tminus_not_lat _ _ _ _ _ hL, FQ_zero_off X hF c L fun h => hL (h _)]


end SysLevel

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section Num

variable {n' k1 : ℕ}

theorem lamI_fin (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n') (i : Fin (k1 + 1)) :
    lamI lam0 s (i.val + 1) = lam0 s i := by
  have hi := i.isLt
  unfold lamI
  rw [dif_pos ⟨by omega, by omega⟩]
  exact congrArg (lam0 s) (Fin.ext (by simp))

theorem sum_head (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n') (r : ℕ) (hr : r ≤ k1 + 1) :
    ∑ i : Fin (k1 + 1) with i.val < r, lam0 s i = ∑ a ∈ Icc 1 r, lamI lam0 s a := by
  refine Finset.sum_bij' (fun i _ => i.val + 1)
    (fun a ha => ⟨a - 1, by rw [Finset.mem_Icc] at ha; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc] at hi ⊢
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc] at ha ⊢
    show a - 1 < r
    omega
  · intro i _
    exact Fin.ext (by simp)
  · intro a ha
    rw [Finset.mem_Icc] at ha
    show a - 1 + 1 = a
    omega
  · intro i _
    exact (lamI_fin lam0 s i).symm

theorem sum_tail (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n') (r : ℕ) (hr : r ≤ k1 + 1) :
    ∑ i : Fin (k1 + 1) with i.val < r, lam0 s i.rev = ∑ a ∈ Icc (k1 + 1 + 1 - r) (k1 + 1), lamI lam0 s a := by
  refine Finset.sum_bij' (fun i _ => i.rev.val + 1)
    (fun a ha => ⟨k1 + 1 - a, by rw [Finset.mem_Icc] at ha; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have := i.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc, Fin.val_rev] at hi ⊢
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc] at ha ⊢
    show k1 + 1 - a < r
    omega
  · intro i _
    have := i.isLt
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  · intro a ha
    rw [Finset.mem_Icc] at ha
    simp only [Fin.val_rev]
    omega
  · intro i _
    exact (lamI_fin lam0 s i.rev).symm

theorem Ar_eq (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (r : ℕ) (hr : r ≤ k1 + 1) :
    Ar r lam0 = Formalism.InvariantFactorPaths.G7.ArZ (univ.filter fun s : Fin n' => ¬ IsOddPos s)
      (univ.filter fun s : Fin n' => IsOddPos s) (fun s a => lamI lam0 s a) (k1 + 1) r := by
  simp only [Formalism.MainNotions.G.Ar, Formalism.InvariantFactorPaths.G7.ArZ]
  conv_rhs => rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : IsOddPos s
  · have hod : ¬ Even s.val := fun he => by
      have := Nat.even_iff.mp he
      unfold IsOddPos at h
      omega
    rw [if_neg (not_not_intro h), if_pos h, zero_sub, ← sum_tail lam0 s r hr, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [lamAt, if_neg hod]
  · have hev : Even s.val := Nat.even_iff.mpr (by unfold IsOddPos at h; omega)
    rw [if_pos h, if_neg h, sub_zero, ← sum_head lam0 s r hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [lamAt, if_pos hev]

end Num

section Main

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def RestTmFQ : Prop := ∀ (v : X.Pl) (i j : ℕ), ∀ F ∈ X.FQ j, X.Tm v i j F ∈ X.FQ j

def TmR (hT : RestTmFQ X) (v : X.Pl) (j i : ℕ) : Module.End X.G.Kf (X.FQ j) :=
  (TmLin X v i j).restrict fun F hF => hT v i j F hF

theorem TmR_coe (hT : RestTmFQ X) (v : X.Pl) (j i : ℕ) (F : X.FQ j) :
    ((TmR X hT v j i F : X.FQ j) : X.Fm j) = X.Tm v i j F := rfl

def KkR (h3b : ∀ j < X.mm, ∀ F ∈ X.FQ j, X.Kz j F ∈ X.FQ (j + 1)) (j : ℕ) :
    X.FQ j →ₗ[X.G.Kf] X.FQ (j + 1) :=
  if h : j < X.mm then (X.Kz j).restrict fun F hF => h3b j h F hF else 0

theorem KkR_coe (h3b : ∀ j < X.mm, ∀ F ∈ X.FQ j, X.Kz j F ∈ X.FQ (j + 1)) {j : ℕ} (hj : j < X.mm)
    (F : X.FQ j) : ((KkR X h3b j F : X.FQ (j + 1)) : X.Fm (j + 1)) = X.Kz j F := by
  rw [KkR, dif_pos hj]
  rfl

theorem Kc_coe (h3b : ∀ j < X.mm, ∀ F ∈ X.FQ j, X.Kz j F ∈ X.FQ (j + 1)) (j : ℕ) (hj : j ≤ X.mm)
    (F : X.FQ 0) :
    ((Formalism.InvariantFactorPaths.G7.Kc (M := fun j => X.FQ j) (KkR X h3b) j F : X.FQ j) : X.Fm j) = X.chainK j F := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h1 : Formalism.InvariantFactorPaths.G7.Kc (M := fun j => X.FQ j) (KkR X h3b) (j + 1) F =
        KkR X h3b j (Formalism.InvariantFactorPaths.G7.Kc (M := fun j => X.FQ j) (KkR X h3b) j F) := rfl
    rw [h1, KkR_coe X h3b (by omega), ih (by omega)]
    rfl

theorem zpow_nu (x : X.G.Kf) (ν : ℕ) (z : ℤ) : (x ^ ν) ^ z = x ^ ((ν : ℤ) * z) := by
  rw [zpow_mul, zpow_natCast]

theorem beFam_eq (v : X.Pl) (x : Fin (X.t + 1)) :
    Formalism.InvariantFactorPaths.G7.beFam ((p : X.G.Kf) ^ (X.G.P.n' v / 2)) (X.t + 1) x = X.qh v x.val := by
  simp only [Formalism.InvariantFactorPaths.G7.beFam, Sys.qh]
  rw [zpow_nu]
  congr 1
  push_cast
  ring

theorem Tt_eq (v : X.Pl) (i j : ℕ) {F : X.Fm j} (hF : F ∈ X.FQ j) :
    X.Tt v i j F = ((p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) j i)) • X.Tm v i j F := by
  unfold Sys.Tt
  split_ifs with hi
  · subst hi
    rw [Tm_zero X v hF]
    simp [Nprime]
  · rfl

end Main

section Main2

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def uExt (u : ℕ → X.G.Kf) : ℕ → X.G.Kf := fun a => if a ∈ Icc 1 X.mm then u a else 1

theorem uExt_eq (u : ℕ → X.G.Kf) {a : ℕ} (ha : a ∈ Icc 1 X.mm) : uExt X u a = u a := by
  unfold uExt
  rw [if_pos ha]

theorem prod_uExt (u : ℕ → X.G.Kf) {j : ℕ} (hj : j ≤ X.mm) :
    ∏ a ∈ Icc 1 j, uExt X u a = ∏ a ∈ Icc 1 j, u a :=
  Finset.prod_congr rfl fun a ha => uExt_eq X u (by rw [Finset.mem_Icc] at ha ⊢; omega)

theorem FFam_eq (v : X.Pl) (u m : ℕ → X.G.Kf) {j : ℕ} (hj : j ≤ X.mm) :
    Formalism.InvariantFactorPaths.G7.FFam ((p : X.G.Kf) ^ (X.G.P.n' v / 2)) X.t
      (fun l => (∏ a ∈ Icc 1 (l - 1), uExt X u a)⁻¹ * m l) j = X.FF v (mHat u m) j := by
  funext x
  have hx := x.1.isLt
  simp only [Formalism.InvariantFactorPaths.G7.FFam, Sys.FF, mHat, beFam_eq, Nat.add_sub_cancel]
  rw [prod_uExt X u (j := (x.1 : ℕ)) (by omega)]
  ring

theorem cCoef_eq (v : X.Pl) (u m : ℕ → X.G.Kf) {j : ℕ} (hj : j ≤ X.mm) (l : ℕ) :
    Formalism.InvariantFactorPaths.G7.cCoef (p : X.G.Kf) (X.G.P.n' v / 2) (univ.filter fun s : Fin (X.G.P.n' v) => ¬ IsOddPos s)
      (univ.filter fun s : Fin (X.G.P.n' v) => IsOddPos s) (fun s a => lamI (X.G.P.lam0 v) s a) (X.w v)
      (fun l => (∏ a ∈ Icc 1 (l - 1), uExt X u a)⁻¹ * m l) (X.G.P.m + 1) X.t X.G.P.r j l =
      X.cl v (mHat u m) j l := by
  simp only [Formalism.InvariantFactorPaths.G7.cCoef, Sys.cl, Formalism.InvariantFactorPaths.G7.hF, FFam_eq X v u m hj, zpow_nu]
  congr 2
  all_goals first
    | rfl
    | (congr 1; simp only [Formalism.InvariantFactorPaths.G7.NN, Formalism.MainNotions.FormalGroupSystem.NN]; push_cast; ring)

theorem Zop_coe (hT : RestTmFQ X) (v : X.Pl) (u m : ℕ → X.G.Kf) {j : ℕ} (hj : j ≤ X.mm) (G : X.FQ j) :
    ((Formalism.InvariantFactorPaths.G7.Zop (p : X.G.Kf) (X.G.P.n' v / 2) (univ.filter fun s : Fin (X.G.P.n' v) => ¬ IsOddPos s)
      (univ.filter fun s : Fin (X.G.P.n' v) => IsOddPos s) (fun s a => lamI (X.G.P.lam0 v) s a) (X.w v)
      (fun l => (∏ a ∈ Icc 1 (l - 1), uExt X u a)⁻¹ * m l) (X.G.P.m + 1) X.t X.G.P.r j
      (fun i => ((∏ a ∈ Icc 1 j, uExt X u a) ^ i)⁻¹ • TmR X hT v j i) G : X.FQ j) : X.Fm j) =
      X.Zop v u (mHat u m) j G.1 := by
  simp only [Formalism.InvariantFactorPaths.G7.Zop, Formalism.InvariantFactorPaths.G7.Ttil, Sys.Zop, Sys.Ttu, LinearMap.sum_apply,
    LinearMap.smul_apply, AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, TmR_coe]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [cCoef_eq X v u m hj l, Tt_eq X v _ j G.2, prod_uExt X u hj, zpow_neg, zpow_natCast]
  congr 1
  exact smul_comm _ _ _

private theorem eval_smul_esymm_eq_pow_mul {K σ : Type} [Field K] [Fintype σ] (c : K) (x : σ → K) (l : ℕ) :
    MvPolynomial.eval (fun s => c * x s) (MvPolynomial.esymm σ K l) =
      c ^ l * MvPolynomial.eval x (MvPolynomial.esymm σ K l) := by
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]

theorem Ci (hT : RestTmFQ X) (h3b : ∀ j < X.mm, ∀ F ∈ X.FQ j, X.Kz j F ∈ X.FQ (j + 1)) (v : X.Pl)
    (u m : ℕ → X.G.Kf) (hu : ∀ l ∈ Icc 1 X.mm, u l ≠ 0)
    (H : ∀ j < X.mm, ∀ i : ℕ, ∀ F ∈ X.FQ j, X.ecal v i (j + 1) (X.Kz j F) =
      (u (j + 1) ^ i) • X.Kz j (∑ l ∈ range (i + 1),
        (MvPolynomial.eval (fun x : Fin (X.t + 1) => m (j + 1) * X.qh v x.val)
          (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F)) :
    ∀ j < X.mm, ∀ F ∈ X.FQ 0, X.Zop v u (mHat u m) (j + 1) (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F) := by
  intro j hj F hF
  have hj1 : j + 1 ≤ X.mm := by omega
  have hr : X.G.P.r ≤ X.G.P.m + 1 := by
    have := (X.std v).two_r
    omega
  have he : ∀ (a i : ℕ) (c : X.G.Kf) (F : X.Fm a),
      (((p : X.G.Kf) ^ (X.G.P.n' v / 2)) ^ (-((i : ℤ) * ((Formalism.InvariantFactorPaths.G7.NN (X.G.P.m + 1) X.t a : ℤ) - i)))) •
        (c • X.Tm v i a F) = c • X.ecal v i a F := by
    intro a i c F
    rw [smul_comm, Sys.ecal, zpow_nu]
    congr 3
    simp only [Formalism.InvariantFactorPaths.G7.NN, Formalism.MainNotions.FormalGroupSystem.NN]
    push_cast
    ring
  have hp : (p : X.G.Kf) ≠ 0 := by
    have hs := X.G.P.setting v
    haveI := hs.frac_alt
    intro h0
    apply hs.p_unif.ne_zero
    apply IsFractionRing.injective (X.G.P.W v) (X.G.P.Qq v)
    apply (X.G.P.ι v).injective
    rw [map_natCast, map_natCast, map_zero, map_zero]
    exact h0
  have key := Formalism.InvariantFactorPaths.G7.theorem_c_i X.G.Kf (Fin (X.G.P.n' v)) (fun j => X.FQ j) (KkR X h3b)
    (fun a i => ((∏ b ∈ Icc 1 a, uExt X u b) ^ i)⁻¹ • TmR X hT v a i) (p : X.G.Kf) (X.G.P.n' v / 2)
    (X.G.P.m + 1) X.t X.G.P.r (j + 1) (univ.filter fun s : Fin (X.G.P.n' v) => ¬ IsOddPos s)
    (univ.filter fun s : Fin (X.G.P.n' v) => IsOddPos s) (fun s a => lamI (X.G.P.lam0 v) s a) (X.w v)
    (fun l => (∏ a ∈ Icc 1 (l - 1), uExt X u a)⁻¹ * m l) hp hr ?hI
  case hI =>
    unfold Formalism.InvariantFactorPaths.G7.Intertwine
    intro j' hj' i
    have hj'm : j' < X.mm := by omega
    have hF' : ∀ l, Formalism.InvariantFactorPaths.G7.eF (fun x : Fin (X.t + 1) => (∏ a ∈ Icc 1 (j' + 1 - 1), uExt X u a)⁻¹ *
        m (j' + 1) * Formalism.InvariantFactorPaths.G7.beFam ((p : X.G.Kf) ^ (X.G.P.n' v / 2)) (X.t + 1) x) l =
        ((∏ a ∈ Icc 1 j', uExt X u a)⁻¹) ^ l * MvPolynomial.eval (fun x : Fin (X.t + 1) => m (j' + 1) * X.qh v x.val)
          (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l) := by
      intro l
      simp only [Formalism.InvariantFactorPaths.G7.eF, beFam_eq, Nat.add_sub_cancel, mul_assoc]
      exact eval_smul_esymm_eq_pow_mul _ _ l
    apply LinearMap.ext
    intro G
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
      AddSubmonoidClass.coe_finset_sum, TmR_coe, KkR_coe X h3b hj'm]
    simp only [he]
    rw [H j' hj'm i _ G.2, smul_smul, ← map_smul (X.Kz j'), Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [smul_smul, smul_smul]
    congr 1
    rw [hF' l, Finset.prod_Icc_succ_top (by omega : 1 ≤ j' + 1), uExt_eq X u (by rw [Finset.mem_Icc]; omega)]
    have hu' : u (j' + 1) ≠ 0 := hu _ (by rw [Finset.mem_Icc]; omega)
    have hl' : l ≤ i := by
      rw [Finset.mem_range] at hl
      omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl'
    have hu'' : u (j' + 1) ^ (l + d) ≠ 0 := pow_ne_zero _ hu'
    rw [Nat.add_sub_cancel_left, mul_pow, mul_inv, mul_assoc ((∏ a ∈ Icc 1 j', uExt X u a) ^ (l + d))⁻¹,
      inv_mul_cancel₀ hu'', mul_one, pow_add, mul_inv, inv_pow]
    ring
  have k2 := congrArg Subtype.val (LinearMap.congr_fun key ⟨F, hF⟩)
  have h0 : (∏ b ∈ Icc 1 0, uExt X u b) = 1 := by simp
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_smul, Zop_coe X hT v u m hj1,
    Kc_coe X h3b (j + 1) hj1, TmR_coe, h0, one_pow, inv_one, one_smul, map_smul] at k2
  rw [← Ar_eq (X.G.P.lam0 v) X.G.P.r hr] at k2
  rw [yv_eq X v F, map_smul]
  exact k2

end Main2

section Assemble

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def RestHecke : Prop :=
  ∀ v, ∃ u m : ℕ → X.G.Kf, (∀ l ∈ Icc 1 X.mm, X.vEqK (u l) 0) ∧ (∀ l ∈ Icc 1 X.mm, X.vEqK (m l) (X.vm v l)) ∧
    ∀ j < X.mm, ∀ i : ℕ, ∀ F ∈ X.FQ j, X.ecal v i (j + 1) (X.Kz j F) =
      (u (j + 1) ^ i) • X.Kz j (∑ l ∈ range (i + 1),
        (MvPolynomial.eval (fun x : Fin (X.t + 1) => m (j + 1) * X.qh v x.val)
          (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F)

theorem alternate_expansion_of_relations (D : Formalism.BasicNotions.D7) (hH : RestHecke X) (hT : RestTmFQ X) (h3b : adm3b D X) (h3 : PointsLemma D X)
    (h2b : MassRatio₂ D X) : KernelCommutationUpToUnits D X := by
  intro v
  obtain ⟨u, m, hu, hm, H⟩ := hH v
  have hmh := vEqK_mHat X v u m hu hm
  have hCi := Ci X hT h3b v u m (fun l hl => vEqK.ne_zero X (hu l hl)) H
  refine ⟨u, m, hu, hm, fun j hj => ⟨H j hj, hCi j hj, ?_, ?_, ?_⟩⟩
  · exact (Cii X v (mHat u m) hmh j hj).1
  · exact (Cii X v (mHat u m) hmh j hj).2
  · exact Ciii X D h3 h2b v u (mHat u m) hu hmh j hj

end Assemble

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
