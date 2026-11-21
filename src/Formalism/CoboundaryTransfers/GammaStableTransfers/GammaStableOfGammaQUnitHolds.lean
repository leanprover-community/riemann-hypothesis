import Formalism.CoboundaryTransfers.StatementAPI
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound

section
noncomputable section

namespace Formalism.CoboundaryTransfers

namespace WachMod

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)

theorem smulO_eq (c : O) (x : D) : c • x = algebraMap O A c • x := by
  rw [algebraMap_smul]

theorem smulO_mem (c : O) {x : D} (hx : x ∈ W.N) : c • x ∈ W.N := by
  rw [smulO_eq (A := A)]; exact W.N.smul_mem _ hx

theorem qInv_of_mem {n : D} (hn : n ∈ W.N) : W.QInv n := W.N.smul_mem _ hn

theorem qInv_zero : W.QInv 0 := by
  simp only [QInv, smul_zero]; exact W.N.zero_mem

theorem qInv_add {y y' : D} (hy : W.QInv y) (hy' : W.QInv y') : W.QInv (y + y') := by
  simp only [QInv, smul_add]; exact W.N.add_mem hy hy'

theorem qInv_sub {y y' : D} (hy : W.QInv y) (hy' : W.QInv y') : W.QInv (y - y') := by
  simp only [QInv, smul_sub]; exact W.N.sub_mem hy hy'

theorem qInv_smul (a : A) {y : D} (hy : W.QInv y) : W.QInv (a • y) := by
  simp only [QInv]; rw [smul_comm]; exact W.N.smul_mem a hy

theorem qInv_smulO (c : O) {y : D} (hy : W.QInv y) : W.QInv (c • y) := by
  rw [smulO_eq (A := A)]; exact W.qInv_smul _ hy


theorem xN_zero : W.XN 0 := ⟨0, W.N.zero_mem, (smul_zero _).symm⟩

theorem xN_add {z z' : D} (hz : W.XN z) (hz' : W.XN z') : W.XN (z + z') := by
  obtain ⟨n, hn, rfl⟩ := hz; obtain ⟨n', hn', rfl⟩ := hz'
  exact ⟨n + n', W.N.add_mem hn hn', (smul_add _ _ _).symm⟩

theorem xN_smul (a : A) {z : D} (hz : W.XN z) : W.XN (a • z) := by
  obtain ⟨n, hn, rfl⟩ := hz
  exact ⟨a • n, W.N.smul_mem a hn, smul_comm _ _ _⟩

theorem xN_smulO (c : O) {z : D} (hz : W.XN z) : W.XN (c • z) := by
  rw [smulO_eq (A := A)]; exact W.xN_smul _ hz

theorem cont_pow_X_pow_eq_zero_of_lt : W.C1 0 0 := ⟨W.qInv_zero, W.xN_zero⟩

theorem isOneCochain_add {y z y' z' : D} (h : W.C1 y z) (h' : W.C1 y' z') : W.C1 (y + y') (z + z') :=
  ⟨W.qInv_add h.1 h'.1, W.xN_add h.2 h'.2⟩

theorem isOneCochain_smul_of_tower (c : O) {y z : D} (h : W.C1 y z) : W.C1 (c • y) (c • z) :=
  ⟨W.qInv_smulO c h.1, W.xN_smulO c h.2⟩

theorem cont_X_pow_pow_eq_zero_of_gt : W.C2 0 := ⟨0, W.qInv_zero, (smul_zero _).symm⟩

theorem isTwoCochain_add {ω ω' : D} (h : W.C2 ω) (h' : W.C2 ω') : W.C2 (ω + ω') := by
  obtain ⟨y, hy, rfl⟩ := h; obtain ⟨y', hy', rfl⟩ := h'
  exact ⟨y + y', W.qInv_add hy hy', (smul_add _ _ _).symm⟩

theorem isTwoCochain_smul (a : A) {ω : D} (h : W.C2 ω) : W.C2 (a • ω) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨a • y, W.qInv_smul a hy, smul_comm _ _ _⟩

theorem d1_apply (y z : D) : W.d1 y z = (W.γ y - y) - (W.φ z - z) := rfl

theorem diffOne_zero : W.d1 0 0 = 0 := by simp [d1]

theorem diffOne_add (y z y' z' : D) : W.d1 (y + y') (z + z') = W.d1 y z + W.d1 y' z' := by
  simp only [d1, map_add]; abel

theorem diffOne_smul_of_tower (c : O) (y z : D) : W.d1 (c • y) (c • z) = c • W.d1 y z := by
  simp only [d1, map_smul, smul_sub]

theorem diffOne_diffZero (x : D) : W.d1 (W.φ x - x) (W.γ x - x) = 0 := by
  simp only [d1, map_sub, W.comm]; abel

theorem isOneCochain_diffZero {x : D} (hx : x ∈ W.N) : W.C1 (W.φ x - x) (W.γ x - x) := by
  refine ⟨?_, ?_⟩
  · simp only [QInv, smul_sub]
    exact W.N.sub_mem (W.φ_N x hx) (W.N.smul_mem _ hx)
  · obtain ⟨x', hx', h⟩ := W.γ_N x hx
    exact ⟨x', hx', h⟩

theorem isTwoCochain_diffOne {y z : D} (h : W.C1 y z) : W.C2 (W.d1 y z) := by
  obtain ⟨hy, n, hn, rfl⟩ := h
  obtain ⟨y', hy', hγ⟩ := W.γ_QN y hy
  obtain ⟨v, hv⟩ := B.φX
  refine ⟨y' - (v • W.φ n - n), ?_, ?_⟩
  · refine W.qInv_sub hy' (W.qInv_sub ?_ (W.qInv_of_mem hn))
    refine W.qInv_smul v ?_
    exact W.φ_N n hn
  · rw [d1, hγ, W.φ_smul, hv, mul_smul, smul_sub, smul_sub]



theorem cocycle_zero : W.Cocycle 0 0 := ⟨W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero⟩

theorem cocycle_add {y z y' z' : D} (h : W.Cocycle y z) (h' : W.Cocycle y' z') :
    W.Cocycle (y + y') (z + z') :=
  ⟨W.isOneCochain_add h.1 h'.1, by rw [W.diffOne_add, h.2, h'.2, add_zero]⟩

theorem cocycle_smulO (c : O) {y z : D} (h : W.Cocycle y z) : W.Cocycle (c • y) (c • z) :=
  ⟨W.isOneCochain_smul_of_tower c h.1, by rw [W.diffOne_smul_of_tower, h.2, smul_zero]⟩

theorem isCob1_zero : W.IsCob1 0 0 := ⟨0, W.N.zero_mem, by simp, by simp⟩

theorem isCob1_add {y z y' z' : D} (h : W.IsCob1 y z) (h' : W.IsCob1 y' z') :
    W.IsCob1 (y + y') (z + z') := by
  obtain ⟨x, hx, rfl, rfl⟩ := h; obtain ⟨x', hx', rfl, rfl⟩ := h'
  refine ⟨x + x', W.N.add_mem hx hx', ?_, ?_⟩ <;> simp only [map_add] <;> abel

theorem isCob1_smulO (c : O) {y z : D} (h : W.IsCob1 y z) : W.IsCob1 (c • y) (c • z) := by
  obtain ⟨x, hx, rfl, rfl⟩ := h
  exact ⟨c • x, W.smulO_mem c hx, by rw [map_smul, smul_sub], by rw [map_smul, smul_sub]⟩

theorem isCob2_zero : W.IsCob2 0 := ⟨0, 0, W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero.symm⟩

theorem isCob2_add {ω ω' : D} (h : W.IsCob2 ω) (h' : W.IsCob2 ω') : W.IsCob2 (ω + ω') := by
  obtain ⟨y, z, hc, rfl⟩ := h; obtain ⟨y', z', hc', rfl⟩ := h'
  exact ⟨y + y', z + z', W.isOneCochain_add hc hc', (W.diffOne_add _ _ _ _).symm⟩

theorem isCob2_smulO (c : O) {ω : D} (h : W.IsCob2 ω) : W.IsCob2 (c • ω) := by
  obtain ⟨y, z, hc, rfl⟩ := h
  exact ⟨c • y, c • z, W.isOneCochain_smul_of_tower c hc, (W.diffOne_smul_of_tower _ _ _).symm⟩

def qInvSub : Submodule A D where
  carrier := {y | W.QInv y}
  add_mem' := W.qInv_add
  zero_mem' := W.qInv_zero
  smul_mem' := fun a _ hy => W.qInv_smul a hy

def xNSub : Submodule A D where
  carrier := {z | W.XN z}
  add_mem' := W.xN_add
  zero_mem' := W.xN_zero
  smul_mem' := fun a _ hz => W.xN_smul a hz

def twoCochains : Submodule A D where
  carrier := {ω | W.C2 ω}
  add_mem' := W.isTwoCochain_add
  zero_mem' := W.cont_X_pow_pow_eq_zero_of_gt
  smul_mem' := fun a _ h => W.isTwoCochain_smul a h

def cocycleSub : Submodule O (D × D) where
  carrier := {pr | W.Cocycle pr.1 pr.2}
  add_mem' := fun h h' => W.cocycle_add h h'
  zero_mem' := W.cocycle_zero
  smul_mem' := fun c _ h => W.cocycle_smulO c h

def isCob1Sub : Submodule O (D × D) where
  carrier := {pr | W.IsCob1 pr.1 pr.2}
  add_mem' := fun h h' => W.isCob1_add h h'
  zero_mem' := W.isCob1_zero
  smul_mem' := fun c _ h => W.isCob1_smulO c h

def isCob2Sub : Submodule O D where
  carrier := {ω | W.IsCob2 ω}
  add_mem' := W.isCob2_add
  zero_mem' := W.isCob2_zero
  smul_mem' := fun c _ h => W.isCob2_smulO c h

theorem mem_Z1_iff_cocycle (y z : D) : (y, z) ∈ W.Z1 ↔ W.d1 y z = 0 := by
  rw [Z1, LinearMap.mem_ker, LinearMap.coprod_apply]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply, d1]
  rw [← sub_eq_add_neg]

theorem mem_cocycles' (pr : D × D) : pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := W.mem_Z1_iff_cocycle pr.1 pr.2


theorem coboundaries_le_cocycles : W.B1 ≤ W.Z1 := by
  rintro _ ⟨x, rfl⟩
  rw [W.mem_cocycles']
  simpa [LinearMap.prod_apply] using W.diffOne_diffZero x





end WachMod




end Formalism.CoboundaryTransfers
end
end

section
noncomputable section

namespace Formalism.CoboundaryTransfers

section SlopeTestRemainingChoices

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

private theorem WachMod.mem_cocycles_units_iff (W : WachMod B M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := by
  simp [WachMod.Z1, WachMod.d1, sub_eq_add_neg]


end SlopeTestRemainingChoices


theorem gammaStableOfGammaQUnit_holds : GammaQNOf := by
  intro O A _ _ _ B M D _ _ _ _ N γ hG hQ hγ hN y hy
  obtain ⟨v, hvu, ⟨t, hvt⟩, hγQ⟩ := hG
  have hit : ∀ (k : ℕ) (x : D), (fun x : D => B.Q • x)^[k] x = B.Q ^ k • x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  have hQM : Function.Bijective (fun x : D => B.Q ^ M • x) := by
    have h := hQ.iterate M
    rwa [show (fun x : D => B.Q • x)^[M] = fun x => B.Q ^ M • x from funext (hit M)] at h
  have hvk : ∀ k : ℕ, ∃ s : A, v ^ k = 1 + B.X * s := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      exact ⟨s + t + B.X * s * t, by rw [pow_succ, hs, hvt]; ring⟩
  obtain ⟨s, hs⟩ := hvk M
  have hγn : γ (B.Q ^ M • y) = v ^ M • B.Q ^ M • γ y := by
    rw [hγ, map_pow, hγQ, mul_pow, mul_smul]
  obtain ⟨n', hn'N, hn'⟩ := hN _ hy
  obtain ⟨u, hu⟩ := hvu.pow M
  have hQγ : B.Q ^ M • γ y ∈ N := by
    have h1 : γ (B.Q ^ M • y) ∈ N := by
      have e : γ (B.Q ^ M • y) = B.Q ^ M • y + B.X • n' := by rw [← hn']; abel
      rw [e]
      exact N.add_mem hy (N.smul_mem _ hn'N)
    have h2 : B.Q ^ M • γ y = ((u⁻¹ : Aˣ) : A) • γ (B.Q ^ M • y) := by
      rw [hγn, ← hu, smul_smul, Units.inv_mul, one_smul]
    rw [h2]
    exact N.smul_mem _ h1
  have hmN : n' - s • B.Q ^ M • γ y ∈ N := N.sub_mem hn'N (N.smul_mem _ hQγ)
  have hkey : B.Q ^ M • (γ y - y) = B.X • (n' - s • B.Q ^ M • γ y) := by
    have e : (1 + B.X * s) • B.Q ^ M • γ y - B.Q ^ M • y = B.X • n' := by
      rw [← hs, ← hγn]
      exact hn'
    rw [smul_sub, smul_sub, ← e, add_smul, one_smul, mul_smul]
    abel
  obtain ⟨y', hy'⟩ := hQM.2 (n' - s • B.Q ^ M • γ y)
  simp only at hy'
  refine ⟨y', by rw [hy']; exact hmN, ?_⟩
  apply hQM.1
  show B.Q ^ M • (γ y - y) = B.Q ^ M • (B.X • y')
  rw [hkey, smul_comm (B.Q ^ M) B.X y', hy']


theorem finiteClassesLift_holds : LiftHf := by
  intro O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g eW c
    hnat hcl₁ hint hlifts κ hκ
  obtain ⟨pr, hcoc, hpr⟩ := hint.2 κ hκ
  obtain ⟨y₁, z₁, hcoc₁, hy, hz⟩ := hlifts _ _ hcoc
  have hmem : ((y₁, z₁) : D₁ × D₁) ∈ W₁.Z1 := (WachMod.mem_cocycles_units_iff W₁ _).mpr hcoc₁.2
  refine ⟨cl₁ ⟨(y₁, z₁), hmem⟩, hcl₁ _ hcoc₁, ?_⟩
  have hpr' : ((c • pr : W₂.Z1) : D₂ × D₂) = S.π.f2 (⟨(y₁, z₁), hmem⟩ : W₁.Z1) := by
    show c • (pr : D₂ × D₂) = (S.π.f y₁, S.π.f z₁)
    rw [hy, hz]
    rfl
  rw [hnat _ _ hpr', map_smul, hpr, smul_smul, mul_comm]

end Formalism.CoboundaryTransfers
end
end
