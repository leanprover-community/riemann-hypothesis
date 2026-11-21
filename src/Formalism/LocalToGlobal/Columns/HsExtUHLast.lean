import Formalism.LocalToGlobal.Columns.TiedXp
import Formalism.LocalToGlobal.Columns.CharactersLevelZeroAgree
import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
import Formalism.LocalToGlobal.HermitianForms.BothLemmas
import Formalism.LocalToGlobal.Columns.TiedXpU

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hp_basePi_one (E : Type) [Field E] [NumberField E] [StarRing E] : BasePi (∅ : Finset (Pl E)) (1 : 𝓞 E) where
  dvd r := ⟨fun _ => one_dvd r, fun _ P hP => absurd hP (Finset.notMem_empty P)⟩
  cop := isCoprime_one_left

theorem hp_baseLb_empty (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) [NeZero n] :
    baseLb E n (∅ : Finset (Pl E)) = stdLat E n := by
  refine le_antisymm (rll_baseLb_le n ∅) fun x hx => ?_
  rw [rll_baseLb_eq n (hp_basePi_one E), rll_mem_dLat]
  rw [mem_stdLat] at hx
  refine ⟨fun i _ => hx i, ?_⟩
  rw [map_one, inv_one, one_mul]
  exact hx _

structure HCrdP (X : Fields) (n : ℕ) [NeZero n] {cls : Type} (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  n' : ℕ
  hn : n' = n
  J : Matrix (Fin n') (Fin n') X.E
  hJ : J = 1
  l0 : Submodule (𝓞 X.E) (Fin n' → X.E)
  hl0 : l0 = Formalism.L2.Forms.reL hn.symm (baseLb X.E n (∅ : Finset (Pl X.E)))
  lat : cls → Submodule (𝓞 X.E) (Fin n' → X.E)
  hlat : ∀ c, lat c = Formalism.L2.Forms.reL hn.symm (L c)

structure LevPackP {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (gp : Fin 2 → ℕ) (Lb : Submodule (𝓞 E) (Fin n → E)) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F))
  Uloc_lev : ∀ v, Uloc v ≤ levelVL hc.sig J v Lb
  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) → ((gp 1 : 𝓞 F) ∉ v.asIdeal) → Uloc v = levelVL hc.sig J v Lb
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F),
    (x ∈ levelVL hc.sig J v Lb ∧ ∀ y ∈ Formalism.L2.Herm.locL v Lb, ∃ z ∈ Formalism.L2.Herm.locL v Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) → x ∈ Uloc v
  U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v
  cls : RecCls hc J Lb U stab lat

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)

def levPackP₁ (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c) :
    LevPackP hc n (1 : Matrix (Fin n) (Fin n) X.E) Pr.g (baseLb X.E n (∅ : Finset (Pl X.E)))
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.N) where
  Uloc := (tieLevP hc σ₀ Λ).Uloc
  Uloc_lev := (tieLevP hc σ₀ Λ).Uloc_lev
  Uloc_hyp := fun v h0 h1 => (tieLevP hc σ₀ Λ).Uloc_hyp v (fun hb => ((th_plUnder_vGs hc hPr v).1 hb).elim h0 h1)
    (fun h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
  Uloc_g := fun i v hv x hx => by
    refine levLoc_of_princ hc n ∅ Pr.vGs Λ.grp v (Pr.g i) ?_ ?_ x hx.1 hx.2
    · rintro ⟨P, hP, _⟩
      exact absurd hP (Finset.notMem_empty P)
    · intro w _ hov
      have : (Pr.g i : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ hv
      rwa [Ideal.mem_comap, map_natCast] at this
  U := (tieLevP hc σ₀ Λ).U
  U_eq := (tieLevP hc σ₀ Λ).U_eq
  cls :=
    { y := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y
      y_bij := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_bij
      y_lat := fun c x => by
        have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_lat c x
        rw [xp_L_eq_N] at h
        exact h
      stabI := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI
      stabI_inj := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_inj
      stabI_range := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_range
      stabI_lat := fun c γ x => by
        have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_lat c γ x
        rw [xp_L_eq_N] at h
        exact h }

def levPackP (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (H : HCrdP X n fun c => (s c).1.N) :
    LevPackP hc H.n' H.J Pr.g H.l0 (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) H.lat := by
  obtain ⟨n', hn, J, rfl, l0, hl0, lat, hlat⟩ := H
  subst hn
  obtain rfl : l0 = baseLb X.E n' (∅ : Finset (Pl X.E)) := hl0.trans (Formalism.L2.Forms.reL_rfl _)
  obtain rfl : lat = fun c => (s c).1.N := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact levPackP₁ hc hPr σ₀ Λ s hS hs

theorem levelPacking_sameCarrier (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (H : HCrdP X n fun c => (s c).1.N) (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) :
    Formalism.L2.Forms.SameCar H.hn H.l0 (clsPG hc σ₀ Λ s hS hs Q).lev.Lb
      (levPackP hc hPr σ₀ Λ s hS hs H).Uloc (clsPG hc σ₀ Λ s hS hs Q).lev.Uloc
      (levPackP hc hPr σ₀ Λ s hS hs H).U (clsPG hc σ₀ Λ s hS hs Q).lev.U
      (fun c => ((levPackP hc hPr σ₀ Λ s hS hs H).cls.y c).1) (fun c => ((clsPG hc σ₀ Λ s hS hs Q).y c).1)
      (fun c t => ((levPackP hc hPr σ₀ Λ s hS hs H).cls.stabI c t).1)
      (fun c t => ((clsPG hc σ₀ Λ s hS hs Q).stabI c t).1) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  obtain ⟨n', hn, J, rfl, l0, hl0, lat, hlat⟩ := H
  subst hn
  obtain rfl : l0 = baseLb X.E n' (∅ : Finset (Pl X.E)) := hl0.trans (Formalism.L2.Forms.reL_rfl _)
  obtain rfl : lat = fun c => (s c).1.N := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_sameCar_refl _ _ _ _ _

theorem levelPacking_stabilizer (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (H : HCrdP X n fun c => (s c).1.N) (c : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp)
    (t : MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) :
    Formalism.L2.Forms.reGL H.hn X.E ((levPackP hc hPr σ₀ Λ s hS hs H).cls.stabI c t).1 = ((ratEquiv hc n).symm t.1.1).1 := by
  obtain ⟨n', hn, J, rfl, l0, hl0, lat, hlat⟩ := H
  subst hn
  obtain rfl : l0 = baseLb X.E n' (∅ : Finset (Pl X.E)) := hl0.trans (Formalism.L2.Forms.reL_rfl _)
  obtain rfl : lat = fun c => (s c).1.N := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact Formalism.L2.Forms.reGL_rfl _ _

end Gen

section Repack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
  {S : HSpace E} {gp : Fin 2 → ℕ} {Lb : Submodule (𝓞 E) (Fin S.rank → E)} {cls : Type} {stab : cls → Type}
  [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}

def LevPackP.toStep (P : LevPackP hc S.rank S.gram gp Lb stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.StepLevel0 hc S gp Lb where
  Uloc := P.Uloc
  Uloc_lev := P.Uloc_lev
  Uloc_hyp := P.Uloc_hyp
  Uloc_g := P.Uloc_g
  U := P.U
  U_eq := P.U_eq

def LevPackP.toCls (P : LevPackP hc S.rank S.gram gp Lb stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.ClassTie hc S Lb P.toStep.U stab lat where
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := fun c γ => P.cls.stabI_range c γ.1 γ.2

end Repack

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem hq_toGLb_mulVec {n : ℕ} (b : Basis (Fin n) E V) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Herm.toGLb b γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ b.equivFun x = b.equivFun (γ x) :=
  LinearMap.toMatrix_mulVec_repr b b (γ : V →ₗ[E] V) x

def hqCrd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) : V ≃ₗ[E] (Fin N → E) :=
  b.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem hq_reGL_mulVec {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x = hqCrd b h (γ x) := by
  subst h
  rw [Formalism.L2.Forms.reGL_rfl]
  exact hq_toGLb_mulVec b γ x

def hqLin {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) : V ≃ₗ[E] V :=
  (Formalism.L2.Herm.toGLb b).symm ((Formalism.L2.Forms.reGL h E).symm g)

theorem hqLin_re {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) :
    Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b (hqLin b h g)) = g := by
  unfold hqLin
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem hqLin_crd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) (x : V) :
    hqCrd b h (hqLin b h g x) = (g : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x := by
  have := hq_reGL_mulVec b h (hqLin b h g) x
  rw [hqLin_re] at this
  exact this.symm

end Mat

section Form

variable {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]

theorem hq_hform_dot (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem hq_hform_UJ (σ : A →+* A) (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) (x y : n → A) :
    hform σ J ((g : Matrix n n A) *ᵥ x) ((g : Matrix n n A) *ᵥ y) = hform σ J x y := by
  have hτ : σ ∘ ((g : Matrix n n A) *ᵥ x) = (g : Matrix n n A).map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ (g : Matrix n n A) x i
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  rw [hq_hform_dot, hq_hform_dot, hτ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  show _ ⬝ᵥ ((cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *ᵥ y) = _
  rw [hg']

end Form

variable {D : ColRec}

theorem hq_crdN (i : ℕ) (hi : i ≤ D.R.m) : CF.crdN D i hi = hqCrd (D.sp.X i).frame (CF.rankN D i hi) := rfl

def hqG (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) : CH.GX D i :=
  ⟨hqLin (D.sp.X i).frame (CF.rankN D i hi) g.1, fun x y => by
    rw [hx_hform i hi, hx_hform i hi, hq_crdN, hqLin_crd, hqLin_crd]
    exact hq_hform_UJ _ _ g.1 g.2 _ _⟩

theorem hqG_crd (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) (x : (D.sp.X i).V) :
    CF.crdN D i hi ((hqG i hi g).1 x) = (g.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ CF.crdN D i hi x :=
  hqLin_crd _ _ g.1 x

theorem hqG_re (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) :
    Formalism.L2.Forms.reGL (CF.rankN D i hi) D.host.E (Formalism.L2.Herm.toGLb (D.sp.X i).frame (hqG i hi g).1) = g.1 :=
  hqLin_re _ _ g.1

theorem hqG_gmap (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi))
    (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    (gmap (hqG i hi g).1 L).map
        ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) =
      Formalism.L2.Forms.mulLat (g.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) (L.map
        ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))) := by
  unfold gmap Formalism.L2.Forms.mulLat
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact hqG_crd i hi g x

theorem hq_map_inj (i : ℕ) (hi : i ≤ D.R.m) : Function.Injective (Submodule.map
    ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))) :=
  Submodule.map_injective_of_injective (CF.crdN D i hi).injective

variable {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} {K : CF.ClsPTied u}

def hqLatP (K : CF.ClsPTied u) (c : (D.fm u).clsP) : Submodule (𝓞 D.host.E) D.sp.X'.V :=
  (K.lat c).map (((CF.crdP D).symm : (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] D.sp.X'.V).restrictScalars (𝓞 D.host.E))

theorem hqLatP_crd (K : CF.ClsPTied u) (c : (D.fm u).clsP) :
    K.lat c = (hqLatP K c).map
      ((CF.crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  unfold hqLatP
  rw [← Submodule.map_comp]
  symm
  convert Submodule.map_id _
  ext x j
  simp

variable (T : CF.TilTied u A K (P D.R.m le_rfl))

def lastSpaceVector : (D.sp.X D.R.m).V := (CF.crdN D D.R.m le_rfl).symm T.z0

theorem lastVector_coords : T.z0 = CF.crdN D D.R.m le_rfl (lastSpaceVector T) := ((CF.crdN D D.R.m le_rfl).apply_symm_apply T.z0).symm

theorem lastVector_mem_span : lastSpaceVector T ∈ Submodule.span D.host.E {D.sp.z} := by
  obtain ⟨a, ha⟩ := T.lastCoordinateUniformizerVector_spans_orthogonal_line
  refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
  unfold lastSpaceVector
  rw [LinearEquiv.eq_symm_apply, map_smul, ha]
  rfl

theorem lastVector_norm : (D.sp.X D.R.m).hT (lastSpaceVector T) (lastSpaceVector T) = ((D.mem u).A.T : D.host.E) := by
  rw [hx_hform D.R.m le_rfl, ← lastVector_coords]
  exact T.hermitianForm_lastCoordinateUniformizerVector_self

def hqTilG (c : (D.fm u).clsP) : CH.GX D D.R.m := hqG D.R.m le_rfl (T.ga c)

set_option maxHeartbeats 1000000 in
theorem hq_til_lat (c : (D.fm u).clsP) :
    gmap (hqTilG T c).1 (D.clsLat u D.R.m ((D.fm u).til c)) =
      (hqLatP K c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {lastSpaceVector T} := by
  apply hq_map_inj D.R.m le_rfl
  rw [hqTilG, hqG_gmap, ← hx_clsCrd, T.til_lat c, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  congr 1
  · unfold hqLatP
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    rfl
  · congr 2
    exact lastVector_coords T

set_option maxHeartbeats 1000000 in
theorem hq_til_fv (c : (D.fm u).clsP) (v : (D.mem u).A.vT) (z : CH.Ld D u D.R.m ((D.fm u).til c)) (a : 𝓞 D.host.E)
    (ha : (a : D.host.E) = (D.sp.X D.R.m).hT (lastSpaceVector T) ((hqTilG T c).1 (z : (D.sp.X D.R.m).V))) :
    (D.fm u).fv D.R.m v _ (hxPr A P D.R.m v _ z) = A.res v a := by
  rw [hxPr_eq A P D.R.m le_rfl]
  refine T.til_fv v c (hxLd D.R.m le_rfl _ z) a ?_
  rw [ha, hx_hform D.R.m le_rfl, ← lastVector_coords, hqTilG, hqG_crd]
  rfl

set_option maxHeartbeats 4000000 in

def xpOf (levP : Formalism.L2.Herm.StepLevel0 D.sp.cm D.sp.X' D.host.g (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0))
    (clsP : Formalism.L2.Herm.ClassTie D.sp.cm D.sp.X' (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ (hqLatP K)) :
    AtTXp A P where
  lattice₂ := hqLatP K
  levP := levP
  clsP := clsP
  z0 := lastSpaceVector T
  cocycle_zero_mem_invariants := lastVector_mem_span T
  hermitianForm_lastCoordinateUniformizerVector_self := lastVector_norm T
  tilG := hqTilG T
  til_tie := fun c => ⟨hq_til_lat T c, fun v z a ha => hq_til_fv T c v z a ha⟩

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d)

theorem gram_eq_one_of_standard (hS : SpStd d.toColBase) : d.sp.X'.gram = 1 := by
  refine Matrix.ext fun x y => ?_
  show d.sp.X'.hT (d.sp.X'.frame x) (d.sp.X'.frame y) = _
  rw [hS.P_on, Matrix.one_apply]

theorem coordLattice_selfDual_auxiliary (hS : SpStd d.toColBase) : Formalism.L2.Herm.crdLat d.sp.X' d.sp.X'.L0 = stdLat d.X.E d.sp.X'.rank := by
  unfold Formalism.L2.Herm.crdLat
  rw [hS.selfDual_span_frame_auxiliary]
  refine th_map_span_std (Formalism.L2.Herm.crd d.sp.X') _ (Equiv.refl _) fun a => ?_
  funext j
  show d.sp.X'.frame.equivFun (d.sp.X'.frame a) j = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext eq_comm

theorem hp_crdLat_map (L : Submodule (𝓞 d.host.E) (Fin (d.R.N d.R.m - 1) → d.host.E)) :
    Formalism.L2.Herm.crdLat d.sp.X' (L.map (((CF.crdP (d.colRec a)).symm :
      (Fin (d.R.N d.R.m - 1) → d.host.E) →ₗ[d.host.E] d.sp.X'.V).restrictScalars (𝓞 d.host.E))) =
      Formalism.L2.Forms.reL (CF.rankP (d.colRec a)).symm L := by
  unfold Formalism.L2.Herm.crdLat Formalism.L2.Forms.reL
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show d.sp.X'.frame.equivFun ((CF.crdP (d.colRec a)).symm x) j = _
  unfold CF.crdP
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

def hCrdP (u : d.what₂.Word) : HCrdP d.X (d.R.N d.R.m - 1) fun c : PCl d => (d.reprP c).1.N where
  n' := d.sp.X'.rank
  hn := CF.rankP (d.colRec a)
  J := d.sp.X'.gram
  hJ := gram_eq_one_of_standard hS
  l0 := Formalism.L2.Herm.crdLat d.sp.X' d.sp.X'.L0
  hl0 := by rw [hp_baseLb_empty, th_reL_std, coordLattice_selfDual_auxiliary hS]
  lat := fun c => Formalism.L2.Herm.crdLat d.sp.X' (hqLatP (parabolicClassAgreement a hS hH hP u) c)
  hlat := fun c => hp_crdLat_map a _

def hermPackP (u : d.what₂.Word) :=
  levPackP d.sp.cm d.hPr d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (hCrdP a hS hH hP u)

set_option maxHeartbeats 4000000 in

def levelExponentAtT (u : d.what₂.Word) : AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) :=
  xpOf (tildeLatticeAgreement a hS hH hP u)
    (LevPackP.toStep (S := d.sp.X') (lat := hqLatP (parabolicClassAgreement a hS hH hP u)) (hermPackP a hS hH hP u))
    (LevPackP.toCls (S := d.sp.X') (lat := hqLatP (parabolicClassAgreement a hS hH hP u)) (hermPackP a hS hH hP u))

theorem th_carP (u : d.what₂.Word) :
    Formalism.L2.Forms.SameCar (CF.rankP (d.colRec a)) (Formalism.L2.Herm.crdLat d.sp.X' d.sp.X'.L0) (parabolicClassAgreement a hS hH hP u).lev.Lb
      (levelExponentAtT a hS hH hP u).levP.Uloc (parabolicClassAgreement a hS hH hP u).lev.Uloc
      (levelExponentAtT a hS hH hP u).levP.U (parabolicClassAgreement a hS hH hP u).lev.U
      (fun c => ((levelExponentAtT a hS hH hP u).clsP.y c).1) (fun c => ((parabolicClassAgreement a hS hH hP u).y c).1)
      (fun c t => ((levelExponentAtT a hS hH hP u).clsP.stabI c t).1) (fun c t => ((parabolicClassAgreement a hS hH hP u).stabI c t).1) :=
  levelPacking_sameCarrier d.sp.cm d.hPr d.σ₀ d.levP.inv d.reprP hP _ (hCrdP a hS hH hP u) (crdPr a hS hH)

theorem th_latP (u : d.what₂.Word) (c : PCl d) :
    (parabolicClassAgreement a hS hH hP u).lat c = ((levelExponentAtT a hS hH hP u).lattice₂ c).map
      ((CF.crdP (d.colRec a) : d.sp.X'.V →ₗ[d.host.E] (Fin (d.R.N d.R.m - 1) → d.host.E)).restrictScalars (𝓞 d.host.E)) :=
  hqLatP_crd (parabolicClassAgreement a hS hH hP u) c

theorem joint_lastVector (u : d.what₂.Word) :
    (tildeLatticeAgreement a hS hH hP u).z0 = CF.crdN (d.colRec a) d.R.m le_rfl (levelExponentAtT a hS hH hP u).z0 :=
  lastVector_coords (tildeLatticeAgreement a hS hH hP u)

theorem th_ga (u : d.what₂.Word) (c : PCl d) :
    ((tildeLatticeAgreement a hS hH hP u).ga c).1 = Formalism.L2.Forms.reGL (CF.rankN (d.colRec a) d.R.m le_rfl) _
      (Formalism.L2.Herm.toGLb (d.sp.X d.R.m).frame ((levelExponentAtT a hS hH hP u).tilG c).1) :=
  (hqG_re d.R.m le_rfl ((tildeLatticeAgreement a hS hH hP u).ga c)).symm

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hs_padL_succ (n : ℕ) : padL E n (n + 1) = incl E n := by
  apply LinearMap.ext
  intro x
  funext j
  rw [padL_apply]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [incl]
  · simp [incl]

theorem hs_extUH_pad {N n : ℕ} (hN : N = n + 1) (g : UF E n) (x : Fin n → E) :
    (extUH hN g).1 (padL E n N x) = padL E n N (g.1 x) := by
  subst hN
  rw [hs_padL_succ]
  show extE g.1 (incl E n x) = incl E n (g.1 x)
  apply sp_ext
  · rw [initL_extE, initL_incl, initL_incl]
  · rw [extE_last]
    simp [incl]

theorem hs_extUH_last {N n : ℕ} (hN : N = n + 1) [NeZero N] (g : UF E n) (p : E) :
    (extUH hN g).1 (Pi.single (lastIdx N) p) = Pi.single (lastIdx N) p := by
  subst hN
  rw [← lastVector_eq_single]
  show extE g.1 (z0 E n p) = z0 E n p
  apply sp_ext
  · rw [initL_extE]
    simp [z0]
  · rw [extE_last]

theorem hs_conj {N : ℕ} (g e : UF E N) (w : Sp E N) : g.1 ((g⁻¹ * e * g⁻¹⁻¹).1 (g.1.symm w)) = e.1 w := by
  rw [inv_inv]
  show g.1 (g.1.symm (e.1 (g.1 (g.1.symm w)))) = e.1 w
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem hs_core {V V' : Type} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V'] {N n : ℕ} (hN : N = n + 1) [NeZero N]
    (e : V ≃ₗ[E] (Fin N → E)) (e' : V' ≃ₗ[E] (Fin n → E)) (ι : V' →ₗ[E] V) (hι : ∀ x, e (ι x) = padL E n N (e' x))
    (γ M : V ≃ₗ[E] V) (S : V' ≃ₗ[E] V') (g₀ : UF E N) (s : UF E n)
    (hγ : ∀ x, e (γ x) = g₀.1 (e x)) (hM : ∀ x, e (M x) = (g₀⁻¹ * extUH hN s * g₀⁻¹⁻¹).1 (e x)) (hSs : ∀ x, e' (S x) = s.1 (e' x))
    (z : V) (p : E) (hz : e z = Pi.single (lastIdx N) p) :
    (∀ x, γ (M (γ.symm (ι x))) = ι (S x)) ∧ γ (M (γ.symm z)) = z := by
  have hγs : ∀ y, e (γ.symm y) = g₀.1.symm (e y) := fun y => by
    rw [LinearEquiv.eq_symm_apply, ← hγ, LinearEquiv.apply_symm_apply]
  constructor
  · intro x
    apply e.injective
    rw [hγ, hM, hγs, hs_conj, hι, hs_extUH_pad, hι, hSs]
  · apply e.injective
    rw [hγ, hM, hγs, hs_conj, hz, hs_extUH_last]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem hs_stab_crd (hc : CMData F E) {V : Type} [AddCommGroup V] [Module E V] {n' n : ℕ} [NeZero n] (b : Basis (Fin n') E V) (h : n' = n)
    (g : GL (Fin n') E) (t : UF E n) (hg : Formalism.L2.Forms.reGL h E g = ((ratEquiv hc n).symm t).1) (x : V) :
    hqCrd b h ((Formalism.L2.Herm.toGLb b).symm g x) = t.1 (hqCrd b h x) := by
  have h1 := hq_reGL_mulVec b h ((Formalism.L2.Herm.toGLb b).symm g) x
  rw [MulEquiv.apply_symm_apply, hg, ← rlc_ratHom_apply hc n] at h1
  have h2 : ratHom hc n ((ratEquiv hc n).symm t) = t := (ratEquiv hc n).apply_symm_apply t
  rw [h2] at h1
  exact h1.symm

end Gen

section GenL

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem levPack_stabI (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp)
    (t : MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) :
    Formalism.L2.Forms.reGL H.hn X.E ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.stabI c t).1 = ((ratEquiv hc n).symm t.1.1).1 := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact Formalism.L2.Forms.reGL_rfl _ _

end GenL

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (hQ : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)

include hS in

theorem hs_iX (x : d.sp.X'.V) :
    CF.crdN (d.colRec a) d.R.m le_rfl (d.sp.iX' x) = padL d.host.E (d.R.N d.R.m - 1) (d.R.N d.R.m) (CF.crdP (d.colRec a) x) := by
  rw [← iXc_eq a hS]
  show _ = CF.crdN (d.colRec a) d.R.m le_rfl (d.sp.iX' ((CF.crdP (d.colRec a)).symm (CF.crdP (d.colRec a) x)))
  rw [LinearEquiv.symm_apply_apply]

theorem hs_tilG (u : d.what₂.Word) (c : PCl d) (x : (d.sp.X d.R.m).V) :
    CF.crdN (d.colRec a) d.R.m le_rfl (((levelExponentAtT a hS hH hP u).tilG c).1 x) =
      (d.tilMv u c).1.1 (CF.crdN (d.colRec a) d.R.m le_rfl x) :=
  (hqG_crd d.R.m le_rfl ((tildeLatticeAgreement a hS hH hP u).ga c) x).trans (tilGa_mulVec u c _)

set_option maxHeartbeats 4000000 in

theorem stabMapTied (disc : ∀ u, AtTDisc (d.colRec a) u)
    (moves : ∀ u, AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)) :
    CH.StabMapTied (d.colRec a) (hermCols a hS hQ hK S hI) (hermAtT a hS hH ⟨disc, moves, levelExponentAtT a hS hH hP⟩) := by
  intro u h1 c s
  exact hs_core (E := d.X.E) (N_m_succ d.R) (CF.crdN (d.colRec a) d.R.m le_rfl) (CF.crdP (d.colRec a)) d.sp.iX' (hs_iX a hS)
    ((levelExponentAtT a hS hH hP u).tilG c).1 _ _ (d.tilMv u c).1 s.1.1 (hs_tilG a hS hH hP u c)
    (fun x => hs_stab_crd d.sp.cm (d.sp.X d.R.m).frame (CF.rankN (d.colRec a) d.R.m le_rfl) _ _
      (levPack_stabI d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) _ _ _ _ (hK u d.R.m) (hCrd hS u d.R.m le_rfl) _
        (stabMapR (Pr := d.Pr) (W := d.W) (Λ := d.lev) (Finset.Subset.refl _) (ΛM := d.levP) d.hPr u (a.piT_off u) a.levExt c s)) x)
    (fun x => hs_stab_crd d.sp.cm d.sp.X'.frame (CF.rankP (d.colRec a)) _ _
      (levelPacking_stabilizer d.sp.cm d.hPr d.σ₀ d.levP.inv d.reprP hP _ (hCrdP a hS hH hP u) c s) x)
    (levelExponentAtT a hS hH hP u).z0 (d.piT u : d.host.E) (joint_lastVector a hS hH hP u).symm

end Rec

end Formalism.L2.Col
end
end
