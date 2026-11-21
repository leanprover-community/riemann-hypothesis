import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierSchurOfRankLeAleph0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_smul_one_of_commute_irreducible_of_countable_rank : ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V), Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
    (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) → (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by
  first | exact @GlobalTheory.dixmier_schur_of_rank_le_aleph0 | exact GlobalTheory.dixmier_schur_of_rank_le_aleph0 | (intros; apply GlobalTheory.dixmier_schur_of_rank_le_aleph0 <;> assumption)
end

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HoweRealKer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {om : Rep σ X W}

theorem thetaSub_ker (hA : GlobalTheory.RealActs.PolActs B M om) {P : Type} [AddCommGroup P] [Module ℂ P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hp : RealQuot B M om p) (hk : GlobalTheory.RealActs.KerStab B M om p) :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (LinearMap.ker p ⊓ M.Pol B.ψ B.emb) := by
  obtain ⟨h1, h2, h3, h4⟩ := hA
  refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨D, hD, hDf⟩ := h1 γ hγ
    have e : f₁ = D f := (hDf f hf f₁).1 hf₁
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hp.lie γ hγ f hf f₁ hf₁), e ▸ hD f hf⟩
  · intro k hk' f hf f₁ hf₁
    obtain ⟨D, hD, hDf⟩ := h2 k hk'
    have e : f₁ = D f := (hDf f hf f₁).1 hf₁
    have hP : f₁ ∈ M.Pol B.ψ B.emb := e ▸ hD f hf
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, sub_mem hP hf⟩
    rw [map_sub, hp.cpt k hk' f hf f₁ hf₁, sub_self]
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨hf0, hfP⟩ := Submodule.mem_inf.1 hf
    obtain ⟨D, hD, hDf⟩ := h3 γ hγ
    have e : f₁ = D f := (hDf f hfP f₁).1 hf₁
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hk.1 γ hγ f hfP f₁ hf₁ (LinearMap.mem_ker.1 hf0)), e ▸ hD f hfP⟩
  · intro k hk' f hf f₁ hf₁
    obtain ⟨hf0, hfP⟩ := Submodule.mem_inf.1 hf
    obtain ⟨D, hD, hDf⟩ := h4 k hk'
    have e : f₁ = D f := (hDf f hfP f₁).1 hf₁
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hk.2 k hk' f hfP f₁ hf₁ (LinearMap.mem_ker.1 hf0)), e ▸ hD f hfP⟩

theorem thetaSub_sup (hA : GlobalTheory.RealActs.PolActs B M om) {N N' : Submodule ℂ (SInf F (Fin n × Fin d))}
    (hN : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N) (hN' : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N') :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (N ⊔ N') := by
  obtain ⟨_, _, h3, h4⟩ := hA
  refine ⟨sup_le hN.1 hN'.1, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ hf₁
    exact Submodule.mem_sup_left (hN.2.1 γ hγ f hf f₁ hf₁)
  · intro k hk f hf f₁ hf₁
    exact Submodule.mem_sup_left (hN.2.2.1 k hk f hf f₁ hf₁)
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
    obtain ⟨D, hD, hDf⟩ := h3 γ hγ
    have hyP := hN.1 hy
    have hzP := hN'.1 hz
    have e : f₁ = D (y + z) := (hDf _ (add_mem hyP hzP) f₁).1 hf₁
    rw [e, map_add]
    exact add_mem (Submodule.mem_sup_left (hN.2.2.2.1 γ hγ y hy (D y) ((hDf y hyP (D y)).2 rfl)))
      (Submodule.mem_sup_right (hN'.2.2.2.1 γ hγ z hz (D z) ((hDf z hzP (D z)).2 rfl)))
  · intro k hk f hf f₁ hf₁
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
    obtain ⟨D, hD, hDf⟩ := h4 k hk
    have hyP := hN.1 hy
    have hzP := hN'.1 hz
    have e : f₁ = D (y + z) := (hDf _ (add_mem hyP hzP) f₁).1 hf₁
    rw [e, map_add]
    exact add_mem (Submodule.mem_sup_left (hN.2.2.2.2 k hk y hy (D y) ((hDf y hyP (D y)).2 rfl)))
      (Submodule.mem_sup_right (hN'.2.2.2.2 k hk z hz (D z) ((hDf z hzP (D z)).2 rfl)))

theorem ker_ne_pol {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hp : RealQuot B M om p) :
    LinearMap.ker p ⊓ M.Pol B.ψ B.emb ≠ M.Pol B.ψ B.emb := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  have hx' : x ∈ (M.Pol B.ψ B.emb).map p := by rw [hp.onto]; exact Submodule.mem_top
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx'
  rw [← h] at hf
  exact hx (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).1)

theorem le_ker_of_ge {P : Type} [AddCommGroup P] [Module ℂ P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hi : GlobalTheory.RealActs.Irred B M om p)
    {N : Submodule ℂ (SInf F (Fin n × Fin d))} (hN : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N)
    (hle : LinearMap.ker p ⊓ M.Pol B.ψ B.emb ≤ N) (hne : N ≠ M.Pol B.ψ B.emb) :
    N ≤ LinearMap.ker p ⊓ M.Pol B.ψ B.emb := by
  have key : ∀ f ∈ M.Pol B.ψ B.emb, p f ∈ N.map p → f ∈ N := by
    intro f hf hpf
    obtain ⟨y, hy, hyf⟩ := Submodule.mem_map.1 hpf
    have h0 : f - y ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hyf, sub_self]), sub_mem hf (hN.1 hy)⟩
    have := add_mem (hle h0) hy
    simpa using this
  rcases hi (N.map p)
      (fun γ hγ f hf f₁ hf₁ hpf => Submodule.mem_map_of_mem (hN.2.2.2.1 γ hγ f (key f hf hpf) f₁ hf₁))
      (fun k hk f hf f₁ hf₁ hpf => Submodule.mem_map_of_mem (hN.2.2.2.2 k hk f (key f hf hpf) f₁ hf₁)) with h | h
  · intro x hx
    have : p x ∈ N.map p := Submodule.mem_map_of_mem hx
    rw [h] at this
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 this), hN.1 hx⟩
  · exact absurd (le_antisymm hN.1 (fun f hf => key f hf (by rw [h]; exact Submodule.mem_top))) hne

theorem ker_eq {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [Nontrivial P] [Nontrivial Q]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} {q : SInf F (Fin n × Fin d) →ₗ[ℂ] Q}
    (hA : GlobalTheory.RealActs.PolActs B M om)
    (hH : ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N' →
      N ≠ M.Pol B.ψ B.emb → N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb)
    (hp : RealQuot B M om p) (hq : RealQuot B M om q) (hkp : GlobalTheory.RealActs.KerStab B M om p)
    (hkq : GlobalTheory.RealActs.KerStab B M om q) (hip : GlobalTheory.RealActs.Irred B M om p) (hiq : GlobalTheory.RealActs.Irred B M om q) :
    LinearMap.ker p ⊓ M.Pol B.ψ B.emb = LinearMap.ker q ⊓ M.Pol B.ψ B.emb := by
  have tp := thetaSub_ker hA hp hkp
  have tq := thetaSub_ker hA hq hkq
  have hS := thetaSub_sup hA tp tq
  have hne := hH _ _ tp tq (ker_ne_pol hp) (ker_ne_pol hq)
  have h1 := le_ker_of_ge hip hS le_sup_left hne
  have h2 := le_ker_of_ge hiq hS le_sup_right hne
  exact le_antisymm (le_sup_left.trans h2) (le_sup_right.trans h1)

theorem exists_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (om : Rep σ X W) (P Q : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (q : SInf F (Fin n × Fin d) →ₗ[ℂ] Q),
    GlobalTheory.RealActs.PolActs B M om →
    (∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N' → N ≠ M.Pol B.ψ B.emb → N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb) →
    RealQuot B M om p → RealQuot B M om q → Nontrivial P → Nontrivial Q → GlobalTheory.RealActs.KerStab B M om p → GlobalTheory.RealActs.KerStab B M om q →
    GlobalTheory.RealActs.Irred B M om p → GlobalTheory.RealActs.Irred B M om q → ∃ ψ : P ≃ₗ[ℂ] Q, ∀ f ∈ M.Pol B.ψ B.emb, q f = ψ (p f) := by
  intro F E _ _ _ _ _ σ B n d X W M om P Q _ _ _ _ p q hA hH hp hq hPn hQn hkp hkq hip hiq
  have hK := ker_eq hA hH hp hq hkp hkq hip hiq
  set Pol := M.Pol B.ψ B.emb
  let p' := p.domRestrict Pol
  let q' := q.domRestrict Pol
  have sp : Function.Surjective p' := by
    intro y
    have hy : y ∈ Pol.map p := by rw [hp.onto]; exact Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨f, hf⟩, rfl⟩
  have sq : Function.Surjective q' := by
    intro y
    have hy : y ∈ Pol.map q := by rw [hq.onto]; exact Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨f, hf⟩, rfl⟩
  have hker : LinearMap.ker p' = LinearMap.ker q' := by
    ext ⟨f, hf⟩
    simp only [p', q', LinearMap.mem_ker, LinearMap.domRestrict_apply]
    have := SetLike.ext_iff.1 hK f
    simp only [Submodule.mem_inf, LinearMap.mem_ker] at this
    constructor
    · intro h; exact (this.1 ⟨h, hf⟩).1
    · intro h; exact (this.2 ⟨h, hf⟩).1
  refine ⟨(p'.quotKerEquivOfSurjective sp).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (q'.quotKerEquivOfSurjective sq)), fun f hf => ?_⟩
  have e1 : (p'.quotKerEquivOfSurjective sp).symm (p f) = Submodule.Quotient.mk ⟨f, hf⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearEquiv.trans_apply, e1, Submodule.quotEquivOfEq_mk]
  rfl

end GlobalTheory.HoweRealKer

end
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_howeDuality_realPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (om : Rep σ X W) (P Q : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (q : SInf F (Fin n × Fin d) →ₗ[ℂ] Q),
    GlobalTheory.RealActs.PolActs B M om →
    (∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N' → N ≠ M.Pol B.ψ B.emb → N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb) →
    RealQuot B M om p → RealQuot B M om q → Nontrivial P → Nontrivial Q → GlobalTheory.RealActs.KerStab B M om p → GlobalTheory.RealActs.KerStab B M om q →
    GlobalTheory.RealActs.Irred B M om p → GlobalTheory.RealActs.Irred B M om q → ∃ ψ : P ≃ₗ[ℂ] Q, ∀ f ∈ M.Pol B.ψ B.emb, q f = ψ (p f) := by
  atlas_forward_decl GlobalTheory.HoweRealKer.exists_equiv
end

section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.RealUniq

open GlobalTheory.RealActs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div' {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_div' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_V (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div' h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div' h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem isPair_V' (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div' h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div' h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem det_ne_zero_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

theorem howe_sup (hKP : KP) {n d r s r' s' : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χY χW : Chr F E}
    {o : Rep σ Y W} (h : IsPair B M χY χW o r s r' s') :
    ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N' → N ≠ M.Pol B.ψ B.emb →
      N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hY : Y.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.herm.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hW : W.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.skew.sig w) (by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])
  exact (hKP.howeDualityReal F E σ h.base.cm n d Y W M B.ψ χY χW o h.base.std h.herm.herm hY h.skew.skew hW h.resX h.resW
    h.hX h.hW h.weil B.emb h.herm.cartan h.skew.cartan).2

variable {κ : Type} [Fintype κ]

theorem actsD_zero (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem acts_zero (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

def induced {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) : V →ₗ[ℂ] V :=
  (π.quotKerEquivOfSurjective hπ).toLinearMap ∘ₗ (LinearMap.ker π).mapQ (LinearMap.ker π) D (fun u hu => hD u hu) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

theorem induced_apply {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) (u : U) :
    induced π hπ D hD (π u) = π (D u) := by
  have e : (π.quotKerEquivOfSurjective hπ).symm (π u) = Submodule.Quotient.mk u := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [induced, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.mapQ_apply]
  rfl

theorem realMaps_unique : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ → ∃ (ψ : R.Pi ≃ₗ[ℂ] R₃.Pi) (l : ℂ), l ≠ 0 ∧
      (∀ f ∈ G.M.Pol B.ψ B.emb, R₃.p f = ψ (R.p f)) ∧ ∀ f ∈ G.M'.Pol B.ψ B.emb, R₃.p' f = l • ψ (R.p' f) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM R₃ hR₃
  have hR := hM.real
  have hPV := isPair_V hM.triple
  have hPV' := isPair_V' hM.triple
  have actV := GlobalTheory.T.polynomial_datum_action_of_pair hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV
  have actV' := GlobalTheory.T.polynomial_datum_action_of_pair hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV'
  have ks_p : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M om R'.p := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ f hf 0 (zero_mem _) f₁ 0 h1 (actsD_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk f hf 0 (zero_mem _) f₁ 0 h1 (acts_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this⟩
  have ks_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M' om' R'.p' := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ 0 (zero_mem _) f hf 0 f₁ (actsD_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk 0 (zero_mem _) f hf 0 f₁ (acts_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm⟩
  have onto' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R'.p' f' = y :=
    fun R' h y => by
      have : y ∈ (G.M'.Pol B.ψ B.emb).map R'.p' := h.quot'.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have onto : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f ∈ G.M.Pol B.ψ B.emb, R'.p f = y :=
    fun R' h y => by
      have : y ∈ (G.M.Pol B.ψ B.emb).map R'.p := h.quot.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have irr_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → Irred B G.M' om' R'.p' := fun R' h N h1 h2 => by
    apply h.irred N
    · intro γ hγ f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.1 γ hγ
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.lie γ hγ f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h1 γ hγ f' hf' (D f') h1' (e ▸ hN)
    · intro k hk f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.2 k hk
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.cpt k hk f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h2 k hk f' hf' (D f') h1' (e ▸ hN)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M om _ _ R.p R₃.p actV (howe_sup hKP hPV) hR.quot hR₃.quot hR.nontriv
    hR₃.nontriv (ks_p R hR) (ks_p R₃ hR₃) hR.irred hR₃.irred
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M' om' _ _ R.p' R₃.p' actV' (howe_sup hKP hPV') hR.quot' hR₃.quot'
    hR.nontriv hR₃.nontriv (ks_p' R hR) (ks_p' R₃ hR₃) (irr_p' R hR) (irr_p' R₃ hR₃)
  choose DL hDLm hDLi using actV.2.2.1
  choose DK hDKm hDKi using actV.2.2.2
  choose DL' hDLm' hDLi' using actV'.2.2.1
  choose DK' hDKm' hDKi' using actV'.2.2.2
  let ι : Type := {γ // γ ∈ Lines σ G.W} ⊕ {k // k ∈ KInf σ G.W B.emb}
  let D : ι → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    Sum.elim (fun γ => DL γ.1 γ.2) (fun k => DK k.1 k.2)
  let D' : ι → SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')) :=
    Sum.elim (fun γ => DL' γ.1 γ.2) (fun k => DK' k.1 k.2)
  have Dm : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, D i f ∈ G.M.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm _ _ f hf, hDKm _ _ f hf]
  have Dm' : ∀ i, ∀ f ∈ G.M'.Pol B.ψ B.emb, D' i f ∈ G.M'.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm' _ _ f hf, hDKm' _ _ f hf]
  have joint : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb,
      ∀ f' ∈ G.M'.Pol B.ψ B.emb, R'.p f = R'.p' f' → R'.p (D i f) = R'.p' (D' i f') := by
    rintro R' h (γ | k) f hf f' hf' e
    · exact h.lie γ.1 γ.2 f hf f' hf' _ _ ((hDLi _ _ f hf _).2 rfl) ((hDLi' _ _ f' hf' _).2 rfl) e
    · exact h.cpt k.1 k.2 f hf f' hf' _ _ ((hDKi _ _ f hf _).2 rfl) ((hDKi' _ _ f' hf' _).2 rfl) e
  have ker0 : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, R.p f = 0 → R.p (D i f) = 0 := by
    rintro (γ | k) f hf h0
    · exact (ks_p R hR).1 γ.1 γ.2 f hf _ ((hDLi _ _ f hf _).2 rfl) h0
    · exact (ks_p R hR).2 k.1 k.2 f hf _ ((hDKi _ _ f hf _).2 rfl) h0
  let π : G.M.Pol B.ψ B.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol B.ψ B.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨f, hf, e⟩ := onto R hR y
    exact ⟨⟨f, hf⟩, e⟩
  let ρ : ι → Module.End ℂ R.Pi := fun i =>
    induced π hπ ((D i).restrict (Dm i)) (fun u hu => ker0 i u.1 u.2 hu)
  have hρ : ∀ i, ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), ρ i (R.p f) = R.p (D i f) := fun i f hf =>
    induced_apply π hπ _ _ ⟨f, hf⟩
  have irrρ : ∀ N : Submodule ℂ R.Pi, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN => by
    apply hR.irred N
    · intro γ hγ f hf f₁ h1 hx
      rw [(hDLi γ hγ f hf f₁).1 h1]
      have := hN (Sum.inl ⟨γ, hγ⟩) _ hx
      rwa [hρ _ f hf] at this
    · intro k hk f hf f₁ h1 hx
      rw [(hDKi k hk f hf f₁).1 h1]
      have := hN (Sum.inr ⟨k, hk⟩) _ hx
      rwa [hρ _ f hf] at this
  let T : Module.End ℂ R.Pi := ψ.symm.toLinearMap ∘ₗ ψ₁.toLinearMap
  have comm : ∀ i, T * ρ i = ρ i * T := fun i => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f', hf', rfl⟩ := onto' R hR x
    obtain ⟨f, hf, e⟩ := onto R hR (R.p' f')
    obtain ⟨g, hg, eg⟩ := onto R₃ hR₃ (R₃.p' f')
    have j1 := joint R hR i f hf f' hf' e
    have j3 := joint R₃ hR₃ i g hg f' hf' eg
    have lhs : T (ρ i (R.p' f')) = R.p (D i g) := by
      calc T (ρ i (R.p' f')) = ψ.symm (ψ₁ (R.p' (D' i f'))) := by rw [← e, hρ i f hf, j1]; rfl
      _ = ψ.symm (R₃.p' (D' i f')) := by rw [← hψ₁ _ (Dm' i f' hf')]
      _ = R.p (D i g) := by rw [← j3, hψ _ (Dm i g hg), LinearEquiv.symm_apply_apply]
    have rhs : ρ i (T (R.p' f')) = R.p (D i g) := by
      calc ρ i (T (R.p' f')) = ρ i (ψ.symm (R₃.p' f')) := by
            show ρ i (ψ.symm (ψ₁ (R.p' f'))) = _
            rw [← hψ₁ f' hf']
      _ = ρ i (R.p g) := by rw [← eg, hψ g hg, LinearEquiv.symm_apply_apply]
      _ = R.p (D i g) := hρ i g hg
    rw [Module.End.mul_apply, Module.End.mul_apply, lhs, rhs]
  have hrank : Module.rank ℂ R.Pi ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_surjective π hπ).trans (GlobalTheory.T.polynomial_data_countable_rank hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV)
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_one_of_commute_irreducible_of_countable_rank R.Pi ι ρ T hR.nontriv hrank irrρ comm
  have hT : ∀ x, T x = c • x := fun x => by rw [hc]; rfl
  refine ⟨ψ, c, ?_, hψ, fun f hf => ?_⟩
  · rintro rfl
    haveI := hR.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
    have h0 : ψ.symm (ψ₁ x) = 0 := by rw [← zero_smul ℂ x, ← hT x]; rfl
    exact hx (ψ₁.injective (ψ.symm.injective (h0.trans (map_zero _).symm) |>.trans (map_zero _).symm))
  · rw [hψ₁ f hf]
    calc ψ₁ (R.p' f) = ψ (T (R.p' f)) := by
          show _ = ψ (ψ.symm (ψ₁ (R.p' f)))
          rw [LinearEquiv.apply_symm_apply]
    _ = c • ψ (R.p' f) := by rw [hT, map_smul]

end GlobalTheory.ThK.RealUniq

end
end
