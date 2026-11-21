import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq
import Formalism.LocalToGlobal.Columns.TargetChF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointDecoratedLatticeAllTwistsStatement

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.DiaPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_row {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (r : Fin n) (K U : Fin n → P.adicCompletion E)
    {c s : 𝓞 E ⧸ P.asIdeal} (hK : ∀ j, HasRes P (K j) (if j = r then c else 0)) (hU : ∀ j, Valued.v (U j) ≤ 1)
    (hs : HasRes P (U r) s) : HasRes P (∑ j, K j * U j) (c * s) := by
  obtain ⟨s, rfl, hs⟩ := hs
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, DilPt.hasRes_mk_iff]
  have hC : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have e : (∑ j, K j * U j) - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (c * s)) =
      ∑ j, (K j - if j = r then algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) else 0) * U j +
        algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) *
          (U r - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      map_mul]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_) ?_
  · rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right' (hU j)) ?_
    have := hK j
    by_cases hj : j = r
    · rw [if_pos hj, DilPt.hasRes_mk_iff] at this
      rwa [if_pos hj]
    · rw [if_neg hj] at this
      rw [if_neg hj, sub_zero]
      exact DilPt.hasRes_lt_one this
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hC) hs

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem decoSet_ext {d d' : DecoSet E n ST SG} (hN : d.1.N = d'.1.N) (hf : ∀ P, ∀ x ∈ d'.1.N, d.1.f P x = d'.1.f P x)
    (hbe : ∀ w, ∀ x ∈ d'.1.N, d.1.be w x = d'.1.be w x) : d = d' := by
  have hat : ∀ P, d.1.at P = d'.1.at P := fun P => by unfold Deco.at; rw [hN]
  have h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E), s ∉ P.asIdeal → Ideal.Quotient.mk P.asIdeal s ≠ 0 :=
    fun P s hs h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  refine Subtype.ext (Deco.ext hN (funext fun P => funext fun x => ?_) (funext fun P => funext fun x => ?_))
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hf P _ h
      rw [d.2.f_smul P s x (hat _ ▸ hx), d'.2.f_smul P s x hx] at this
      have hp := P.1.isPrime
      exact mul_left_cancel₀ (h0 _ s hs) this
    · rw [d.2.f_off P x (hat _ ▸ hx), d'.2.f_off P x hx]
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hbe P _ h
      rw [d.2.be_smul P s x (hat _ ▸ hx), d'.2.be_smul P s x hx] at this
      have hp := P.1.isPrime
      funext i
      exact mul_left_cancel₀ (h0 _ s hs) (congrFun this i)
    · rw [d.2.be_off P x (hat _ ▸ hx), d'.2.be_off P x hx]

theorem decoOf_dia_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g k : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) (c : DiaG E ST), IsPtOf hc (g * k) p → (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = Formalism.L2.Col.stdLat E n) → (∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → g ∈ UAd hc n ∧ (decoOf ST SG g).dia c = p.deco := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g k p c h ⟨p₀, hk, hk0⟩ htriv hrow
  classical
  have hg : g ∈ UAd hc n := by
    have := mul_mem h.uni (inv_mem hk.uni)
    rw [mul_inv_cancel_right] at this
    exact this
  have hkc := hk.lat
  rw [hk0] at hkc
  have hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E :=
    fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))
  have hN : Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) p.deco.2.lat.span_eq_top]
    ext w
    refine (mem_globLat g w).trans ((hkI _).trans ?_)
    have e : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Formalism.L2.Col.pullV g w =
        GlobalTheory.Mem.Col2.pullV (g * k) w := (DilPt.pullbackVector_mul_right g k w).symm
    rw [e]
    refine (mem_latS_std _).symm.trans ((h.lat _).symm.trans ?_)
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hone : ∀ w ∈ SG, ∀ i j, adAt F w ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if j = i then 1 else 0 := by
    intro w hw i j
    have h1 : bc (prV (E := E) (w.under (𝓞 F))) k⁻¹ = 1 := by rw [map_inv, htriv w hw, inv_one]
    have h2 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0 := by
      have := congrArg (fun x : GL (Fin n) _ => x.1 i j) h1
      simp only [Units.val_one, Matrix.one_apply] at this
      exact this
    have h3 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j - if j = i then 1 else 0) = 0 := by
      rw [map_sub, h2]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    have h4 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E _ _).1.1 h3 w rfl
    rw [map_sub, sub_eq_zero] at h4
    rw [h4]
    split_ifs <;> simp
  have hraw := rlc_decoOf_val hc n ST SG hg
  have hint : ∀ x ∈ p.deco.1.N, ∀ i, GlobalTheory.Mem.Col2.pullV g x i ∈ RInt F E := fun x hx =>
    (mem_globLat g x).1 (hN ▸ hx)
  refine ⟨hg, decoSet_ext ?_ (fun P x hx => ?_) fun w x hx => ?_⟩
  · show (decoOf ST SG g).1.N = _
    rw [hraw]
    exact hN
  · show (c P).1 * (decoOf ST SG g).1.f P x = _
    have hl : (lastIdx n).1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
    have h1 := h.f P x hx _ hl
    rw [DilPt.pullbackVector_mul_right] at h1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1
    have h2 := hasRes_row (lastIdx n) _ (fun j => adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x j)) (fun j => hrow P _ j hl)
      (fun j => (mem_rInt_iff F E _).1 (hint x hx j) P.1) (PtExist.hasRes_redA P.1 (hint x hx _))
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    exact h2.unique h1
  · show (decoOf ST SG g).1.be w x = _
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    funext i
    have h1 := h.be w x hx i
    rw [DilPt.pullbackVector_mul_right] at h1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hone w.1 w.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    exact (PtExist.hasRes_redA w.1 (hint x hx i)).unique h1

end GlobalTheory.Mem.Col2.DiaPt
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g k : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) (c : DiaG E ST), IsPtOf hc (g * k) p → (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → g ∈ UAd hc n ∧ (decoOf ST SG g).dia c = p.deco := by
  atlas_forward_decl GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_diagonal_basePoint_levelPrime : ∀ {B : Base} (X : PreX B.toPre), (B.primes X).Ok → ∀ (u : B.Word) (n : ℕ), ∃ k : GA B n, (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) ∧ (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) ∧ ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := by
  first | exact @GlobalTheory.Mem.Col2.BasePoint.exists_kStd | exact GlobalTheory.Mem.Col2.BasePoint.exists_kStd | (intros; apply GlobalTheory.Mem.Col2.BasePoint.exists_kStd <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetInFrames_eq_iff_reduction_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, cosetIn q = cosetIn q' ↔ MemChart.bar q = MemChart.bar q' := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.cosetIn_eq_iff_bar_eq | exact GlobalTheory.Mem.Col2.MemChart.cosetIn_eq_iff_bar_eq | (intros; apply GlobalTheory.Mem.Col2.MemChart.cosetIn_eq_iff_bar_eq <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

theorem inv_smul_mem_of_be_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.at w.1) (h0 : d.be w x = 0) :
    ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • x ∈ d.at w.1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TopStep.liftFr_spec hd w
  set fr := d.liftFr w with hfr
  have e : fr (fr.symm x) = x := fr.apply_symm_apply x
  have hs : fr.symm x ∈ stdAt E n w.1 := (h1 _).1 (by rwa [e])
  have hr := h2 _ hs
  rw [e, h0] at hr
  have hi := GlobalTheory.TopStep.mem_stdAt.1 hs
  have hs' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • fr.symm x ∈ stdAt E n w.1 := GlobalTheory.TopStep.mem_stdAt.2 fun i => by
    have := GlobalTheory.TopStep.intAt_div_of_redP hq (hi i) (congrFun hr i).symm
    rwa [div_eq_inv_mul] at this
  have := (h1 _).2 hs'
  rwa [map_smul, e] at this

theorem sub_mem_of_be_eq {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {y y' z : Sp E n}
    (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.at w.1) (hy' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y' ∈ d.at w.1)
    (hz : z - y' ∈ d.at w.1)
    (e : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)) :
    y - y' ∈ d.at w.1 := by
  have hq0 : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hqz : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y') ∈ d.at w.1 :=
    GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) hz
  have e1 : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y')) = 0 := by
    rw [GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) hz, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul]
  have e2 := hd.be_add w _ hqz _ hy'
  rw [← smul_add, sub_add_cancel, e1, zero_add, ← e] at e2
  have hx : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (y - y') ∈ d.at w.1 := by
    rw [smul_sub]
    exact sub_mem hy hy'
  have e3 := hd.be_add w _ hx _ hy'
  rw [← smul_add, sub_add_cancel, e2, right_eq_add] at e3
  have := inv_smul_mem_of_be_eq_zero hd w hq hx e3
  rwa [smul_smul, inv_mul_cancel₀ hq0, one_smul] at this

theorem mem_coset {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] {L : Submodule A M} {y z : M} :
    z ∈ {z | z - y ∈ L} ↔ z - y ∈ L := Iff.rfl

theorem coset_eq {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] (L : Submodule A M) {y y' : M} (h : y - y' ∈ L) :
    {z | z - y ∈ L} = {z | z - y' ∈ L} := by
  refine Set.ext fun z => ?_
  rw [mem_coset, mem_coset]
  refine ⟨fun h' => ?_, fun h' => ?_⟩
  · have := add_mem h' h
    rwa [sub_add_sub_cancel] at this
  · have := sub_mem h' h
    rwa [sub_sub_sub_cancel_right] at this

theorem eq_of_deco_bar : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, q.1.1.deco = q'.1.1.deco → MemChart.bar q = MemChart.bar q' → q = q' := by
  intro X Pr R sel S mu cst u j hQ hq q q' hd hb
  have hP : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P => by
    have := P.2
    simpa [rowSG, uSG, hQ] using this
  have hfr : q.1.1 = q'.1.1 := by
    apply Subtype.ext
    have hE : ∀ a, a ∈ QE sel (mu : Chr X.F X.E X.K) → False := fun a ha => by
      rw [hQ] at ha
      simp at ha
    exact Prod.ext hd (funext fun P => (hE _ P.2).elim)
  suffices h2 : q.1.2 = q'.1.2 from Subtype.ext (Prod.ext hfr h2)
  by_cases hj : j + 1 = R.m
  · obtain ⟨y, hy, eY⟩ := q.mem_ybSet hj
    obtain ⟨y', hy', eY'⟩ := q'.mem_ybSet hj
    have eN : q'.1.1.deco.1.N = q.1.1.deco.1.N := by rw [hd]
    rw [eN] at hy' eY'
    have key : ∀ e : rowSG Pr sel mu → ℤ, (∀ P, e P = 0) → y - y' ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N e := by
      intro e he
      refine (mem_locLat _ _ _ _).2 fun P => ?_
      rw [he P, zpow_zero, inv_one, one_smul]
      have hm : q.1.1.deco.1.be ⟨P.1, hP P⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar q ⟨P.1, hP P⟩ :=
        ⟨y, by rw [eY, mem_coset, sub_self]; exact zero_mem _, rfl⟩
      rw [congrFun hb ⟨P.1, hP P⟩] at hm
      obtain ⟨z, hz, ez⟩ := hm
      rw [← hd] at ez
      rw [eY'] at hz
      have hz' := (mem_locLat _ _ _ _).1 (mem_coset.1 hz) P
      rw [if_pos (hP P), zpow_zero, inv_one, one_smul] at hz'
      have h1 := (mem_locLat _ _ _ _).1 hy P
      have h2 := (mem_locLat _ _ _ _).1 hy' P
      rw [if_pos (hP P), _root_.zpow_neg_one, inv_inv] at h1 h2
      exact sub_mem_of_be_eq q.1.1.deco.2 ⟨P.1, hP P⟩ (hq _ (hP P)) h1 h2 hz' ez
    rw [eY, eY']
    exact coset_eq _ (key _ fun P => if_pos (hP P))
  · have h1 := q.2
    have h1' := q'.2
    rw [ysAt_ys_of_ne sel mu cst hj] at h1 h1'
    exact h1.trans h1'.symm

end GlobalTheory.Mem.Col2.MemChart
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnPoint_eq_of_deco_and_cosetReduction : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, q.1.1.deco = q'.1.1.deco → MemChart.bar q = MemChart.bar q' → q = q' := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar | exact GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar | (intros; apply GlobalTheory.Mem.Col2.MemChart.eq_of_deco_bar <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart.CosetLift

section Local

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_div (P : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ K : ℕ, ∀ e ∈ P.asIdeal ^ K, Formalism.L2.Col.IntAt P (algebraMap (𝓞 E) E e / (m : E)) := by
  have h0 : P.intValuation (m : 𝓞 E) ≠ 0 := P.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hm)
  refine ⟨(-WithZero.log (P.intValuation (m : 𝓞 E))).toNat, fun e he => ?_⟩
  have hv : P.valuation E (algebraMap (𝓞 E) E e / (m : E)) ≤ 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E) m, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    have h1 := (P.intValuation_le_pow_iff_mem e _).2 he
    have h2 : WithZero.exp (-((-WithZero.log (P.intValuation (m : 𝓞 E))).toNat : ℤ)) ≤ P.intValuation (m : 𝓞 E) := by
      conv_rhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
    exact (div_le_one₀ (zero_lt_iff.2 h0)).2 (h1.trans h2)
  obtain ⟨r, s, hrs⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hrs⟩

theorem exists_one_intAt_div (T : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ e : 𝓞 E, Ideal.Quotient.mk w.asIdeal e = 1 ∧
      ∀ w' ∈ T, w' ≠ w → Formalism.L2.Col.IntAt w' (algebraMap (𝓞 E) E e / (m : E)) := by
  classical
  choose K hK using fun w' : HeightOneSpectrum (𝓞 E) => exists_pow_intAt_div w' hm
  have ht : ∀ w' : HeightOneSpectrum (𝓞 E), ∃ t : 𝓞 E, t ∉ w.asIdeal ∧ (w' ≠ w → t ∈ w'.asIdeal) := by
    intro w'
    by_cases hne : w' = w
    · exact ⟨1, Formalism.L2.Col.one_notMem w, fun h => absurd hne h⟩
    · by_contra hc
      refine hne (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top fun t h => ?_))
      by_contra h'
      exact hc ⟨t, h', fun _ => h⟩
  choose t ht1 ht2 using ht
  have := w.isMaximal
  have := w.isPrime
  have he0 : (∏ w' ∈ T, t w' ^ K w') ∉ w.asIdeal :=
    w.asIdeal.primeCompl.prod_mem fun w' _ => w.asIdeal.primeCompl.pow_mem (ht1 w') _
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (Formalism.L2.Col.mk_ne_zero he0)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨(∏ w' ∈ T, t w' ^ K w') * b, by rw [map_mul, hb], fun w' hw' hne => hK w' _ (Ideal.mul_mem_right _ _ ?_)⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w' => t w' ^ K w') hw'
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (ht2 w' hne) _)

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem exists_vec (d : DecoSet E n ST SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) :
    ∃ y : Sp E n, ∀ w : SG, ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1 ∧
      d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = v w := by
  classical
  choose x hxN hxv using fun w : SG => d.2.be_surj w (v w)
  choose e he1 he2 using fun w : SG => exists_one_intAt_div SG w.1 (m := Formalism.L2.Col.qOf w.1)
    (Nat.cast_ne_zero.1 (TopStep.qOf_ne_zero (P := w.1)))
  refine ⟨∑ w : SG, (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E)) • x w, fun w0 => ?_⟩
  have hc : ((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w0) / ((Formalism.L2.Col.qOf w0.1 : ℕ) : E)) =
      algebraMap (𝓞 E) E (e w0) := mul_div_cancel₀ _ TopStep.qOf_ne_zero
  have hi : ∀ w : SG, Formalism.L2.Col.IntAt w0.1
      (((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E))) := fun w => by
    by_cases h : w = w0
    · rw [h, hc]
      exact Formalism.L2.Col.IntAt.coe _ _
    · exact (TopStep.intAt_nat _).mul (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm))
  have hx : ∀ w : SG, x w ∈ d.1.at w0.1 := fun w => Formalism.L2.Col.le_locP _ _ (hxN w)
  simp only [Finset.smul_sum, smul_smul]
  refine ⟨Submodule.sum_mem _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), ?_⟩
  rw [TopStep.be_sum d.2 w0 _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), Finset.sum_eq_single w0]
  · rw [TopStep.be_smul_int d.2 w0 (hi w0) (hx w0), hc, Formalism.L2.Col.reduction_coe, he1, one_smul, hxv]
  · intro w _ h
    rw [TopStep.be_smul_int d.2 w0 (hi w) (hx w), Formalism.L2.Col.reduction_mul (TopStep.intAt_nat _)
      (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm)), TopStep.reduction_absNorm_eq_zero, zero_mul, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem coset_be (d : DecoSet E n ST SG) (SB : Finset (HeightOneSpectrum (𝓞 E))) (w : SG) (hw : w.1 ∈ SB) (e0 : SB → ℤ)
    (h0 : e0 ⟨w.1, hw⟩ = 0) {y : Sp E n} (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1) :
    {v | ∃ z ∈ {z | z - y ∈ Formalism.L2.Col.locLat SB d.1.N e0}, v = d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)} =
      {d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y)} := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z - y ∈ d.1.at w.1 := by
      have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hz ⟨w.1, hw⟩
      rwa [h0, zpow_zero, inv_one, one_smul] at this
    have e : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z =
        ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y + ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [Set.mem_singleton_iff, e, d.2.be_add w _ hy _ (TopStep.smul_mem_locP (TopStep.intAt_nat _) hz'),
      TopStep.be_smul_int d.2 w (TopStep.intAt_nat _) hz', TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · intro hv
    exact ⟨y, by rw [Set.mem_setOf_eq, sub_self]; exact zero_mem _, hv⟩

end Local

theorem exists_ptAt_bar_eq {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (_hq : ∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2)
    (q : PtAt R sel mu cst u j) (d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) :
    ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  classical
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
    have hG : ∀ w : Pr.vGs, w.1 ∈ rowSG Pr sel mu := fun w => Finset.mem_union_left _ w.2
    have hG' : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P =>
      (Finset.mem_union.mp P.2).resolve_right fun h' => chfok_false hQ ⟨P.1, h'⟩
    obtain ⟨y', hy'⟩ := exists_vec d fun w => q.1.1.deco.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : X.E) • y)
    refine ⟨⟨(chfokLift hQ d, {z | z - y' ∈ Formalism.L2.Col.locLat (rowSG Pr sel mu) d.1.N
      (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), ?_⟩, rfl, ?_⟩
    · rw [ysAt_ys_of_eq sel mu cst h]
      refine ⟨y', (Formalism.L2.Col.mem_locLat _ _ _ _).2 fun P => ?_, by congr!⟩
      rw [if_pos (hG' P), _root_.zpow_neg_one, inv_inv]
      exact (hy' ⟨P.1, hG' P⟩).1
    · funext w
      have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w.1, hG w⟩
      rw [if_pos w.2, _root_.zpow_neg_one, inv_inv] at h1
      refine (coset_be d _ w (hG w) _ (if_pos w.2) (hy' w).1).trans ?_
      rw [(hy' w).2, MemChart.bar, hY]
      exact (coset_be q.1.1.deco _ w (hG w) _ (if_pos w.2) h1).symm
  · have hY : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne sel mu cst h] at this
    refine ⟨⟨(chfokLift hQ d, ∅), by rw [ysAt_ys_of_ne sel mu cst h]; rfl⟩, rfl, ?_⟩
    funext w
    simp [MemChart.bar, hY]

end GlobalTheory.Mem.Col2.MemChart.CosetLift
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_couplingCoset_with_given_reduction : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ (q : PtAt R sel mu cst u j) (d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs), ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.CosetLift.exists_ptAt_bar_eq | exact GlobalTheory.Mem.Col2.MemChart.CosetLift.exists_ptAt_bar_eq | (intros; apply GlobalTheory.Mem.Col2.MemChart.CosetLift.exists_ptAt_bar_eq <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.MemChart

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG : Finset (Pl E)}

theorem ufGL_ratHom (γ : URat hc n) : ufGL E n (ratHom hc n γ) = γ.1 := by
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← rlc_ratHom_apply]
  show LinearMap.toMatrix' _ *ᵥ _ = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem ufGL_mem (g : UF E n) : ufGL E n g ∈ URat hc n := by
  obtain ⟨γ, rfl⟩ := (ratHom_bijective hc n).2 g
  rw [ufGL_ratHom]
  exact γ.2

include hc in
theorem ufGL_inj : Function.Injective (ufGL E n) := fun a b h => by
  obtain ⟨γ, rfl⟩ := (ratHom_bijective hc n).2 a
  obtain ⟨δ, rfl⟩ := (ratHom_bijective hc n).2 b
  rw [ufGL_ratHom, ufGL_ratHom] at h
  rw [Subtype.ext h]

theorem cls_dia (H : Subgroup (GLG E n SG)) (c : DiaG E ST) (d d' : DecoSet E n ST SG) :
    decoCls n ST SG H (d.dia c) = decoCls n ST SG H (d'.dia c) ↔ decoCls n ST SG H d = decoCls n ST SG H d' := by
  rw [rla_cls_eq, rla_cls_eq]
  refine exists_congr fun g => ?_
  rw [← rla_dia_smulH]
  exact ⟨rla_dia_inj n ST SG c, fun h => by rw [h]⟩

theorem chart_exists (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ}
    (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T)
    (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ)
    (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = plUnder F SG)
    {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (c₀ : DiaG E ST)
    (s : cl → DecoSet E n ST SG) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n)
    (hd : ∀ c, (decoOf ST SG (y c)).dia c₀ = s c)
    (hs : Function.Bijective fun c => decoCls n ST SG (Subgroup.pi Set.univ Hw) (s c)) (hlat : ∀ c, lat c = (s c).1.L)
    (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c))
    (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)), ufGL E n g.1 = γ ∧ g • s c = s c) :
    ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F))
      (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J),
      Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧
      (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
        x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
        ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧
      (∀ c, Function.Injective (SI c)) ∧
      (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧
      lev.Lb = baseLb E n ST ∧ lev.U = levU hc n ST SG (Subgroup.pi Set.univ Hw) ∧
      (∀ (x : lev.U) (h : x.1 ∈ levU hc n ST SG (Subgroup.pi Set.univ Hw)), lev.chi x = levTyp lam ⟨x.1, h⟩) ∧
      (∀ c, (Y c).1 = y c) ∧ ∀ c a, (SI c a).1 = st c a := by
  subst hJ hb
  have hm : ∀ c a, st c a ∈ URat hc n := fun c a => by
    obtain ⟨g, hg, -⟩ := (hr c _).1 ⟨a, rfl⟩
    rw [← hg]
    exact ufGL_mem hc n _
  have hd' : ∀ c, decoOf ST SG (y c) = (s c).dia c₀⁻¹ := fun c => by rw [← hd, rla_dia_inv']
  refine ⟨stepOf hc n Hw hB hTπ hST hcard hSG hidx lam, fun c => ⟨y c, hy c⟩, fun c => (st c).codRestrict _ (hm c), ?_, fun c x => ?_,
    fun c a b h => hinj c (congrArg Subtype.val h), fun c γ => ?_, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  · have hA := adToCls_injective hc n ST SG (Subgroup.pi Set.univ Hw)
    have key : ∀ c, adToCls hc n ST SG (Subgroup.pi Set.univ Hw) (Quotient.mk'' (⟨y c, hy c⟩ : UAd hc n)) =
        decoCls n ST SG (Subgroup.pi Set.univ Hw) ((s c).dia c₀⁻¹) := fun c => by
      rw [adToCls_mk]
      exact congrArg _ (hd' c)
    constructor
    · intro c c' e
      have e' : (Quotient.mk'' (⟨y c, hy c⟩ : UAd hc n) : AdCl hc n ST SG (Subgroup.pi Set.univ Hw)) =
        Quotient.mk'' (⟨y c', hy c'⟩ : UAd hc n) := e
      have := congrArg (adToCls hc n ST SG (Subgroup.pi Set.univ Hw)) e'
      rw [key, key, cls_dia] at this
      exact hs.1 this
    · intro q
      induction q using Quotient.inductionOn' with
      | h x =>
        obtain ⟨c, hc'⟩ := hs.2 (decoCls n ST SG (Subgroup.pi Set.univ Hw) ((decoOf ST SG x.1).dia c₀))
        refine ⟨c, hA ?_⟩
        refine (key c).trans (Eq.trans ?_ (adToCls_mk hc n ST SG _ x).symm)
        rw [← cls_dia n _ c₀, rla_dia_inv]
        exact hc'
  · have h := decoRaw_carries hc n ST SG (hy c) x
    rw [← rlc_decoOf_val hc n ST SG (hy c), hd', DecoSet.dia_L, ← hlat] at h
    exact h
  · refine Iff.trans ?_ (stabRat_rangeD hc n ST SG (Subgroup.pi Set.univ Hw) c₀ (s c) ⟨y c, hy c⟩ (hd c) γ)
    rw [rla_mem_range_stabRat]
    refine Iff.trans (b := γ.1 ∈ (st c).range) ⟨fun ⟨a, h⟩ => ⟨a, congrArg Subtype.val h⟩, fun ⟨a, h⟩ => ⟨a, Subtype.ext h⟩⟩ ?_
    rw [hr]
    constructor
    · rintro ⟨⟨g, h⟩, e, hg⟩
      have : g = ratHom hc n γ := ufGL_inj hc n (e.trans (ufGL_ratHom hc n γ).symm)
      subst this
      exact ⟨h, hg⟩
    · rintro ⟨h, hg⟩
      exact ⟨(_, h), ufGL_ratHom hc n γ, hg⟩

theorem red_of_act (c₀ : DiaG E ST) {y x : GL (Fin n) (AfE F E)} (hy : y ∈ UAd hc n) (hx : y * x ∈ UAd hc n) (h : GLG E n SG)
    (e : (decoOf ST SG (y * x)).dia c₀ = ((1, h) : UF E n × GLG E n SG) • (decoOf ST SG y).dia c₀) :
    ∃ hJ : x ∈ J0 hc n ST, redG hc n ST SG ⟨x, hJ⟩ = h⁻¹ := by
  have e1 : decoOf ST SG (y * x) = ((1, h) : UF E n × GLG E n SG) • decoOf ST SG y := rla_dia_inj n ST SG c₀ e
  have e2 : decoRaw ST SG (y * x) = (decoRaw ST SG y).act 1 h := by
    rw [← rlc_decoOf_val hc n ST SG hx, ← rlc_decoOf_val hc n ST SG hy, e1]
    rfl
  obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG hx hy h e2
  have e3 : x = ((y * x)⁻¹ * y)⁻¹ := by group
  refine ⟨e3 ▸ inv_mem hJ, ?_⟩
  rw [← hr, ← map_inv]
  exact congrArg _ (Subtype.ext e3)

theorem act_of_mem (H : Subgroup (GLG E n SG)) (c₀ : DiaG E ST) {y : GL (Fin n) (AfE F E)} (hy : y ∈ UAd hc n) (x : levU hc n ST SG H) :
    (decoOf ST SG (y * x.1)).dia c₀ =
      ((1, ((Formalism.L2.Col.levRed hc n ST SG H x)⁻¹ : H).1) : UF E n × GLG E n SG) • (decoOf ST SG y).dia c₀ := by
  have h := rlc_decoOf_sm hc n ST SG H 1 x⁻¹ ⟨y, hy⟩
  rw [map_one, map_inv] at h
  simp only [OneMemClass.coe_one, map_one, one_mul, InvMemClass.coe_inv, inv_inv] at h
  rw [h]
  rfl

end Gen

section Mid

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

def ya (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (g : FrmG Λ Θ) (q : PtY ST SG Q y) : PtY ST SG Q y :=
  (ptYAct y Λ Θ).smul g q


theorem bar_ya (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (g : FrmG Λ Θ) (q : PtY ST SG Q y) (w : SG) :
    bar (ya Λ Θ g q) w = (fun v => (g.2.1.1 w).1 *ᵥ v) '' bar q w := by
  have key : ∀ z, (ya Λ Θ g q).1.1.deco.1.be w ((Formalism.L2.Col.qOf w.1 : X.E) • g.1.1 z) =
      (g.2.1.1 w).1 *ᵥ q.1.1.deco.1.be w ((Formalism.L2.Col.qOf w.1 : X.E) • z) := fun z => by
    show (g.2.1.1 w).1 *ᵥ q.1.1.deco.1.be w (g.1.1.symm _) = _
    rw [← map_smul, LinearEquiv.symm_apply_apply]
  ext v
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, (key z).symm⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, (key z).symm⟩

theorem image_eq_iff {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) (h : GL (Fin n) κ) :
    (fun v => h.1 *ᵥ v) '' C = C ↔ h ∈ setStab C := by
  have hi : ∀ v, (h⁻¹).1 *ᵥ (h.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hi' : ∀ v, h.1 *ᵥ ((h⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro e v
    conv_lhs => rw [← e]
    constructor
    · rintro ⟨v', h1, h2⟩
      have := congrArg (fun v => (h⁻¹).1 *ᵥ v) h2
      simp only [hi] at this
      exact this ▸ h1
    · exact fun hv => ⟨v, hv, rfl⟩
  · intro e
    ext v
    constructor
    · rintro ⟨v', h1, rfl⟩
      exact (e v').2 h1
    · exact fun hv => ⟨_, (e _).1 (by rw [hi']; exact hv), hi' v⟩

theorem bar_ya_eq_iff (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (g : FrmG Λ Θ) (q : PtY ST SG Q y) :
    bar (ya Λ Θ g q) = bar q ↔ ∀ w, g.2.1.1 w ∈ setStab (bar q w) := by
  rw [funext_iff]
  exact forall_congr' fun w => by rw [bar_ya, image_eq_iff]

def chH (Λ : LevFam X.E X.K n SG) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (w : SG) :
    Subgroup (GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) := (Λ w).H ⊓ setStab (C w)

abbrev chG (Λ : LevFam X.E X.K n SG) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) : Subgroup (GLG X.E n SG) :=
  Subgroup.pi Set.univ (chH Λ C)

theorem chG_le (Λ : LevFam X.E X.K n SG) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) : chG Λ C ≤ Λ.grp :=
  fun _ h w hw => (h w hw).1

theorem mem_chG {Λ : LevFam X.E X.K n SG} {C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)} {h : GLG X.E n SG} :
    h ∈ chG Λ C ↔ h ∈ Λ.grp ∧ ∀ w, h w ∈ setStab (C w) :=
  ⟨fun a => ⟨chG_le Λ C a, fun w => (a w trivial).2⟩, fun a w hw => ⟨a.1 w hw, a.2 w⟩⟩

def chLam (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) : chG Λ C →* ℂˣ :=
  (Units.map σ.toMonoidHom).comp (Λ.chr.comp (Subgroup.inclusion (chG_le Λ C)))

theorem decoF_ext (hQ : Q = ∅) {p p' : DecoF X.E n ST SG Q} (h : p.deco = p'.deco) : p = p' := by
  subst hQ
  exact Subtype.ext (Prod.ext h (funext fun P => absurd P.2 (Finset.notMem_empty _)))

theorem grpQ_eq_one (hQ : Q = ∅) (Θ : LevQFam X.E X.K n Q) (t : Θ.grp) : t = 1 := by
  subst hQ
  exact Subtype.ext (funext fun P => absurd P.2 (Finset.notMem_empty _))

variable [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E)

theorem lev_iff (hQ : Q = ∅) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (c₀ : DiaG X.E ST)
    {g x : GL (Fin n) (AfE X.F X.E)} (hg : g ∈ UAd hc n) (hx : g * x ∈ UAd hc n) (q : DecoF X.E n ST SG Q)
    (e : (decoOf ST SG g).dia c₀ = r.1.1.deco) (e' : (decoOf ST SG (g * x)).dia c₀ = q.deco) :
    x ∈ levU hc n ST SG (chG Λ (bar r)) ↔
      ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ (ya Λ Θ κ r).1.1 = q ∧ bar (ya Λ Θ κ r) = bar r := by
  constructor
  · intro h
    have h1 := act_of_mem hc n _ c₀ hg ⟨x, h⟩
    rw [e, e'] at h1
    have h2 := mem_chG.1 ((Formalism.L2.Col.levRed hc n ST SG _ ⟨x, h⟩)⁻¹).2
    refine ⟨(1, ⟨_, h2.1⟩, 1), map_one _, decoF_ext hQ h1.symm, (bar_ya_eq_iff _ _ _ _).2 h2.2⟩
  · rintro ⟨⟨γ, h, t⟩, h1, h2, h3⟩
    have : γ = 1 := ufGL_inj hc n (h1.trans (map_one _).symm)
    subst this
    obtain ⟨hJ, hr⟩ := red_of_act hc n c₀ hg hx h.1 (by rw [e, e', ← h2]; rfl)
    refine (mem_levU hc n ST SG _).2 ⟨hJ, ?_⟩
    rw [hr]
    exact inv_mem (mem_chG.2 ⟨h.2, (bar_ya_eq_iff _ _ _ _).1 h3⟩)

theorem chr_eq (σ : X.K →+* ℂ) (hQ : Q = ∅) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (c₀ : DiaG X.E ST)
    (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    {g : GL (Fin n) (AfE X.F X.E)} (x : levU hc n ST SG (chG Λ C)) (hg : g ∈ UAd hc n) (κ : FrmG Λ Θ) (h1 : ufGL X.E n κ.1 = 1)
    (e : (decoOf ST SG g).dia c₀ = r.1.1.deco) (e' : (decoOf ST SG (g * x.1)).dia c₀ = (ya Λ Θ κ r).1.1.deco) :
    ((levTyp (chLam σ Λ C) x : ℂˣ) : ℂ) = σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K) := by
  obtain ⟨γ, h, t⟩ := κ
  have : γ = 1 := ufGL_inj hc n (h1.trans (map_one _).symm)
  subst this
  obtain ⟨hJ, hr⟩ := red_of_act hc n c₀ hg (mul_mem hg (levU_le_UAd hc n ST SG _ x.2)) h.1 (by rw [e, e']; rfl)
  have h2 : Subgroup.inclusion (chG_le Λ C) (Formalism.L2.Col.levRed hc n ST SG _ x) = h⁻¹ := Subtype.ext hr
  show ((Units.map σ.toMonoidHom (Λ.chr (Subgroup.inclusion (chG_le Λ C) (Formalism.L2.Col.levRed hc n ST SG _ x))))⁻¹ : ℂˣ).1 = _
  rw [h2, grpQ_eq_one hQ Θ t, map_one, mul_one, map_inv, map_inv, inv_inv]
  rfl

end Mid

section Normal

theorem prefRep_normal {G D A : Type} [Group G] [MulAction G D] [Nonempty A] (f : D → A) (pref : D → Prop)
    (hp : ∀ q, pref q ↔ f q = Classical.epsilon fun r => ∃ g : G, r = f (g • q)) (q : D) :
    f (prefRep (G := G) pref (Quotient.mk _ q)) = Classical.epsilon fun r => ∃ g : G, r = f (g • q) := by
  have key : ∀ p, Quotient.mk (MulAction.orbitRel G D) p = Quotient.mk _ q →
      (fun r => ∃ g : G, r = f (g • p)) = fun r => ∃ g : G, r = f (g • q) := fun p h => by
    obtain ⟨a, rfl⟩ : ∃ a : G, a • q = p := MulAction.orbitRel_apply.1 (Quotient.exact h)
    funext r
    refine propext ⟨fun ⟨g, e⟩ => ⟨g * a, by rw [mul_smul]; exact e⟩, fun ⟨g, e⟩ => ⟨g * a⁻¹, ?_⟩⟩
    rw [mul_smul, inv_smul_smul]
    exact e
  have hex : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = Quotient.mk _ q ∧ pref p := by
    obtain ⟨g, e⟩ := Classical.epsilon_spec (p := fun r => ∃ g : G, r = f (g • q)) ⟨_, 1, rfl⟩
    have h : Quotient.mk (MulAction.orbitRel G D) (g • q) = Quotient.mk _ q := Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, rfl⟩)
    exact ⟨g • q, h, (hp _).2 (by rw [key _ h]; exact e.symm)⟩
  unfold prefRep
  rw [dif_pos hex, (hp _).1 hex.choose_spec.2, key _ hex.choose_spec.1]

end Normal

section Orb

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β]
  (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop)

abbrev stR : GStep X.E X.K n := (stepY ST y β Λ Θ p₀).reRep pref

def rp (c : (stR Λ Θ p₀ pref).Cl) : PtY ST SG Q y := (stR Λ Θ p₀ pref).rep c

theorem cl_rp (c : (stR Λ Θ p₀ pref).Cl) : (stR Λ Θ p₀ pref).cl c.1 (rp Λ Θ p₀ pref c) = c := by
  obtain ⟨b, q⟩ := c
  exact congrArg (Sigma.mk b) ((stR Λ Θ p₀ pref).rp_spec b q)

theorem cl_ya (b : β) (g : FrmG (Λ b) (Θ b)) (q : PtY ST SG Q y) :
    (stR Λ Θ p₀ pref).cl b (ya (Λ b) (Θ b) g q) = (stR Λ Θ p₀ pref).cl b q :=
  congrArg (Sigma.mk b) (Quotient.sound ((@MulAction.orbitRel_apply _ _ _ (ptYAct y (Λ b) (Θ b)) _ _).2 ⟨g, rfl⟩))

theorem exists_ya (b : β) (q : PtY ST SG Q y) :
    ∃ g : FrmG (Λ b) (Θ b), rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b q) = ya (Λ b) (Θ b) g q := by
  obtain ⟨g, hg⟩ := (stR Λ Θ p₀ pref).exists_mv b q
  exact ⟨g⁻¹, (@eq_inv_smul_iff _ _ _ (ptYAct y (Λ b) (Θ b)) _ _ _).2 hg⟩

variable [NeZero n] (hinj : ∀ q q' : PtY ST SG Q y, q.1.1.deco = q'.1.1.deco → bar q = bar q' → q = q')

include hinj in
omit [NeZero n] in
theorem ya_eq (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (q q' : PtY ST SG Q y) (hb : bar q' = bar q)
    (g : UF X.E n × chG Λ (bar q)) (hg : g • q.1.1.deco = q'.1.1.deco) :
    ya Λ Θ (g.1, ⟨g.2.1, chG_le _ _ g.2.2⟩, 1) q = q' :=
  hinj _ _ hg (((bar_ya_eq_iff _ _ _ _).2 (mem_chG.1 g.2.2).2).trans hb.symm)

include hinj in
theorem cls_bij (hsur : ∀ (q : PtY ST SG Q y) (d : DecoSet X.E n ST SG), ∃ q' : PtY ST SG Q y, q'.1.1.deco = d ∧ bar q' = bar q)
    (hnorm : ∀ b q q', bar q = bar q' →
      bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b q)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b q')))
    (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop)
    (hp : ∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀)) :
    Function.Bijective fun c : {c // p c} =>
      decoCls n ST SG (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (rp Λ Θ p₀ pref c.1).1.1.deco := by
  constructor
  · rintro ⟨c, h⟩ ⟨c', h'⟩ e
    obtain ⟨h1, h2⟩ := (hp c).1 h
    obtain ⟨h1', h2'⟩ := (hp c').1 h'
    apply Subtype.ext
    show c = c'
    have e1 : decoCls n ST SG (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (rp Λ Θ p₀ pref c).1.1.deco =
      decoCls n ST SG (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (rp Λ Θ p₀ pref c').1.1.deco := e
    rw [← h2'] at e1 h2
    obtain ⟨g, hg⟩ := (rla_cls_eq n ST SG _).1 e1
    have e2 := ya_eq hinj (Λ c₀.1) (Θ c₀.1) _ _ h2 g hg
    have e3 := cl_ya Λ Θ p₀ pref c₀.1 (g.1, ⟨g.2.1, chG_le _ _ g.2.2⟩, 1) (rp Λ Θ p₀ pref c')
    rw [e2] at e3
    have e4 := cl_rp Λ Θ p₀ pref c
    have e5 := cl_rp Λ Θ p₀ pref c'
    have t : ∀ b b' : β, b = b' → ∀ q : PtY ST SG Q y, (stR Λ Θ p₀ pref).cl b q = (stR Λ Θ p₀ pref).cl b' q := by
      rintro b _ rfl q
      rfl
    exact e4.symm.trans ((t _ _ h1 _).trans (e3.trans ((t _ _ h1' _).symm.trans e5)))
  · intro z
    induction z using Quotient.inductionOn' with
    | h d =>
      obtain ⟨q, h1, h2⟩ := hsur (rp Λ Θ p₀ pref c₀) d
      have h3 := hnorm c₀.1 _ _ h2
      rw [cl_rp] at h3
      refine ⟨⟨(stR Λ Θ p₀ pref).cl c₀.1 q, (hp _).2 ⟨rfl, h3⟩⟩, ?_⟩
      obtain ⟨g, hg⟩ := exists_ya Λ Θ p₀ pref c₀.1 q
      rw [hg, ← h2, bar_ya_eq_iff, h2] at h3
      refine (rla_cls_eq n ST SG _).2 ⟨(g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, h3⟩⟩), ?_⟩
      show _ = (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl c₀.1 q)).1.1.deco
      rw [hg, ← h1]
      rfl

def stM (c : (stR Λ Θ p₀ pref).Cl) : (stR Λ Θ p₀ pref).Stab c →* GL (Fin n) X.E :=
  ((stR Λ Θ p₀ pref).gam c.1).comp (Subgroup.subtype _)

include hinj in
omit [NeZero n] in
theorem stM_range (c : (stR Λ Θ p₀ pref).Cl) (b : β) (hb : c.1 = b) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (hC : bar (rp Λ Θ p₀ pref c) = C) (γ : GL (Fin n) X.E) :
    γ ∈ (stM Λ Θ p₀ pref c).range ↔ ∃ g : UF X.E n × chG (Λ b) C, ufGL X.E n g.1 = γ ∧
      g • (rp Λ Θ p₀ pref c).1.1.deco = (rp Λ Θ p₀ pref c).1.1.deco := by
  subst hb hC
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    replace hg : ya (Λ c.1) (Θ c.1) g (rp Λ Θ p₀ pref c) = rp Λ Θ p₀ pref c := hg
    refine ⟨(g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, (bar_ya_eq_iff _ _ _ _).1 (congrArg bar hg)⟩⟩), rfl, ?_⟩
    exact congrArg (fun q : PtY ST SG Q y => q.1.1.deco) hg
  · rintro ⟨g, rfl, hg⟩
    exact ⟨⟨_, ya_eq hinj (Λ c.1) (Θ c.1) _ _ rfl g hg⟩, rfl⟩

omit [NeZero n] in
theorem stM_inj (h : (stR Λ Θ p₀ pref).Ok) (c : (stR Λ Θ p₀ pref).Cl) : Function.Injective (stM Λ Θ p₀ pref c) :=
  (injective_iff_map_eq_one _).2 fun a ha => Subtype.ext (h.stab_inj c.1 a.1 _ a.2 ha)

end Orb

section Main

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev lvG (i : ℕ) := levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i

abbrev lvQ (i : ℕ) := levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i

abbrev rpI (u : B.Word) (i : ℕ) (c : (I.stp u I.mu0 i).Cl) : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i :=
  rp (lvG I i) (lvQ I i) ((I.Tp I.mu0).pref u i) (I.pref u I.mu0 i) c

theorem hqG (hPr : (B.primes X).Ok) : ∀ w ∈ (B.primes X).vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 B.fields.E) ∉ w.asIdeal ^ 2 :=
  fun _ hw => GlobalTheory.TopStep.qOf_notMem_sq (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr hw

theorem cos_iff (hPr : (B.primes X).Ok) {u : B.Word} {i : ℕ} (q q' : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i) :
    cosetIn q = cosetIn q' ↔ bar q = bar q' := GlobalTheory.T.couplingCosetInFrames_eq_iff_reduction_eq I.twistPrimes_reference_tuple_eq_empty (hqG hPr) q q'

theorem cos_of_ne {u : B.Word} {i : ℕ} (h : i + 1 ≠ B.R.m) (q q' : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i) :
    cosetIn q = cosetIn q' := by
  have key : ∀ q : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i, cosetIn q = fun _ => ∅ := fun q => by
    have h1 : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne _ _ _ h] at this
    funext P
    unfold cosetIn
    rw [h1]
    simp
  rw [key, key]

theorem bar_norm (hPr : (B.primes X).Ok) (u : B.Word) (i : ℕ) (b : (I.stp u I.mu0 i).β)
    (q q' : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i) (h : bar q = bar q') :
    bar (rpI I u i ((I.stp u I.mu0 i).cl b q)) = bar (rpI I u i ((I.stp u I.mu0 i).cl b q')) := by
  rw [← cos_iff I hPr]
  by_cases hi : i + 1 = B.R.m
  swap
  · exact cos_of_ne I hi _ _
  have hm := B.R.two_le_m
  have key := @prefRep_normal _ _ _ _ ((I.stp0 u I.mu0 i).actD b) ⟨cosetIn q⟩ (fun q' => cosetIn q') (I.pref u I.mu0 i b) fun p =>
    ⟨fun h => h.2.1 hi, fun h => ⟨fun h0 => by omega, fun _ => h, fun h0 => by omega⟩⟩
  refine (key q).trans (Eq.trans ?_ (key q').symm)
  congr 1
  funext r
  refine propext (exists_congr fun g => ?_)
  have : cosetIn (ya (lvG I i b) (lvQ I i b) g q) = cosetIn (ya (lvG I i b) (lvQ I i b) g q') := by
    rw [cos_iff I hPr]
    funext w
    rw [bar_ya, bar_ya, h]
  exact this ▸ Iff.rfl

theorem kStd_spec (hPr : (B.primes X).Ok) (u : B.Word) (n : ℕ) :
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (kStd X u n) p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) (kStd X u n) = 1) ∧
    ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 (((kStd X u n)⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) :=
  Classical.epsilon_spec (GlobalTheory.T.exists_unitary_diagonal_basePoint_levelPrime X hPr u n)

theorem yStd_spec (hI : I.Ok) (u : B.Word) (i : ℕ) (c : (I.stp u I.mu0 i).Cl) :
    PtOf (I.yStd u i c * kStd X u (B.R.N i)) (extTo I.SQ ((I.stp u I.mu0 i).rep c).1.1) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists I hI u _ (extTo I.SQ ((I.stp u I.mu0 i).rep c).1.1)
  exact Classical.epsilon_spec (p := fun g : GA B (B.R.N i) => PtOf (g * kStd X u (B.R.N i)) (extTo I.SQ ((I.stp u I.mu0 i).rep c).1.1))
    ⟨g * (kStd X u (B.R.N i))⁻¹, by rwa [inv_mul_cancel_right]⟩

theorem dia_of_pt (hPr : (B.primes X).Ok) (u : B.Word) {n : ℕ} [NeZero n] {Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))} {g : GA B n}
    {p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs Q} (h : PtOf (g * kStd X u n) p) :
    g ∈ UAd B.sp.cm n ∧ (decoOf ((B.primes X).vT u) (B.primes X).vGs g).dia (diaT (Pr := B.primes X) u) = p.deco := by
  obtain ⟨k1, k2, k3⟩ := kStd_spec hPr u n
  refine GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul _ _ B.sp.cm n _ _ Q g _ p _ h k1 (fun w hw => k2 _ fun hT => ?_) fun P r j hr => ?_
  · exact rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩
  · have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u))) := by
      have h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0 := fun h0 =>
        (basePi_of_ok (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u).conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact @Ne.isUnit (Res P.1) _ _ h0
    have e : ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) =
        Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by
      unfold diaT
      rw [dif_pos hu]
      rfl
    rw [e]
    exact k3 P r j hr

set_option maxHeartbeats 1000000 in

theorem chart_of (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m)
    (c₀ : (I.stp u I.mu0 i).Cl) (p : (I.stp u I.mu0 i).Cl → Prop)
    (hp : ∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rpI I u i c) = bar (rpI I u i c₀)) :
    ∃ K : LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // p c} => (I.chain l u I.mu0).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1)),
      K.lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u) ∧
      (id K.lev.U : Subgroup (GA B (B.R.N i))) = levU (F := B.host.F) B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (chG (lvG I i c₀.1) (bar (rpI I u i c₀))) ∧
      (∀ (x : K.lev.U) (h : (id x.1 : GA B (B.R.N i)) ∈ levU (F := B.host.F) B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (chG (lvG I i c₀.1) (bar (rpI I u i c₀)))),
        K.lev.chi x = levTyp (F := B.host.F) (hc := B.sp.cm) (chLam (X := B.fields) B.embLL (lvG I i c₀.1) (bar (rpI I u i c₀))) ⟨id x.1, h⟩) ∧
      (∀ c, (K.y c).1 = I.yStd u i c.1) ∧ ∀ c a, (K.stabI c a).1 = (I.stp u I.mu0 i).gam c.1.1 a.1 := by
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  obtain ⟨hg, -, hl⟩ := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 i hi
  have hf : B.fields.f = B.R.f := (hPr.vT_card u).symm.trans (l.lev u I.mu0).card_ST
  have hinj := GlobalTheory.T.columnPoint_eq_of_deco_and_cosetReduction (R := B.R) (cst := I.cst I.mu0) (u := u) (j := i) I.twistPrimes_reference_tuple_eq_empty (hqG hPr)
  have hsur := GlobalTheory.T.exists_couplingCoset_with_given_reduction (R := B.R) (cst := I.cst I.mu0) (u := u) (j := i) I.twistPrimes_reference_tuple_eq_empty (hqG hPr)
  obtain ⟨lev, Y, SI, h1, h2, h3, h4, h5⟩ := chart_exists (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N i)
    (chH (X := B.fields) (lvG I i c₀.1) (bar (rpI I u i c₀))) (f := B.R.f)
    (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = B.T u)) (rls_T_notUnder hPr u)
    (hf ▸ colBase_index (X := B.fields) B.sp.cm (B.R.N i) hPr u) (chLam (X := B.fields) B.embLL (lvG I i c₀.1) (bar (rpI I u i c₀)))
    (gramN (I.rec7 l Z) i hi) hg (badG (I.rec7 l Z)) (Set.ext fun v => (plUnder_vGs (X := B.fields) B.sp.cm hPr v).symm)
    (fun c : {c // p c} => (I.stp u I.mu0 i).Stab c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))
    (diaT (Pr := B.primes X) u) (fun c => (rpI I u i c.1).1.1.deco) (fun c => I.yStd u i c.1)
    (fun c => (dia_of_pt hPr u (yStd_spec I hI u i c.1)).1) (fun c => (dia_of_pt hPr u (yStd_spec I hI u i c.1)).2)
    (cls_bij (lvG I i) (lvQ I i) _ _ hinj hsur (bar_norm I hPr u i) c₀ p hp) (fun c => (hl u I.mu0).1 c.1)
    (fun c => stM (lvG I i) (lvQ I i) _ _ c.1) (fun c => stM_inj (lvG I i) (lvQ I i) _ _ ((l.ch u I.mu0).step i) c.1)
    (fun c γ => stM_range (lvG I i) (lvQ I i) _ _ hinj c.1 c₀.1 ((hp c.1).1 c.2).1 _ ((hp c.1).1 c.2).2 γ)
  exact ⟨⟨lev, Y, h1, h2, SI, h3, h4⟩, h5⟩

theorem levU_congr {u : B.Word} {i : ℕ} {b b' : (I.stp u I.mu0 i).β} (hb : b = b')
    {C C' : ∀ w : (B.primes X).vGs, Set (Fin (B.R.N i) → 𝓞 B.fields.E ⧸ w.1.asIdeal)} (hC : C = C') :
    levU B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (chG (lvG I i b) C) =
      levU B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (chG (lvG I i b') C') := by
  rw [hb, hC]

theorem chr_congr (hPr : (B.primes X).Ok) (hI : I.Ok) {u : B.Word} {i : ℕ} (c : (I.stp u I.mu0 i).Cl) (b : (I.stp u I.mu0 i).β) (hb : c.1 = b)
    (C : ∀ w : (B.primes X).vGs, Set (Fin (B.R.N i) → 𝓞 B.fields.E ⧸ w.1.asIdeal))
    (x : levU B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs (chG (lvG I i b) C)) (κ : (I.stp u I.mu0 i).G c.1)
    (h1 : (I.stp u I.mu0 i).gam c.1 κ = 1)
    (h2 : PtOf (I.yStd u i c * x.1 * kStd X u (B.R.N i)) ((I.stp u I.mu0 i).act c.1 κ ((I.stp u I.mu0 i).rep c)).1.1) :
    ((levTyp (chLam (X := B.fields) B.embLL (lvG I i b) C) x : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 i).chr c.1 κ : B.LLˣ) : B.LL) := by
  subst hb
  exact chr_eq (X := B.fields) B.sp.cm B.embLL I.twistPrimes_reference_tuple_eq_empty (lvG I i c.1) (lvQ I i c.1) (rpI I u i c) _ C x
    (dia_of_pt hPr u (yStd_spec I hI u i c)).1 κ h1 (dia_of_pt hPr u (yStd_spec I hI u i c)).2 (dia_of_pt hPr u h2).2

theorem mem_baseLb (hPr : (B.primes X).Ok) (u : B.Word) (n : ℕ) [NeZero n] (x : Fin n → B.host.E) :
    x ∈ baseLb B.fields.E n ((B.primes X).vT u) ↔ x ∈ baseL B n (X.piT u) := by
  have hB := basePi_of_ok (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u
  have hn := NeZero.ne n
  rw [rlc_mem_baseLb]
  constructor
  · rintro ⟨r, h1, h2⟩ j
    refine ⟨r j, (h1 j).symm, fun hj => ?_⟩
    have e : j = lastIdx n := Fin.ext (by simp only [lastIdx]; omega)
    rw [e]
    exact (hB.dvd _).1 h2
  · intro h
    choose r h1 h2 using h
    exact ⟨r, fun j => (h1 j).symm, (hB.dvd _).2 (h2 _ (by simp only [lastIdx]; omega))⟩

set_option maxHeartbeats 1000000 in

theorem exists_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m), ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u I.mu0 i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), I.ReadsK l Z u I.mu0 i hi chOf K ∧ (∀ c, ((K (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c) ∧ ((i = 0 ∨ i = B.R.m) → Nonempty (Unique Ch)) := by
  intro B X I hI hP l Z u i hi
  have hPr := l.pr
  let φ : (I.stp u I.mu0 i).Cl → (I.stp u I.mu0 i).β × (rowSG (B.primes X) I.sel (I.tup I.mu0) → Set (Sp B.fields.E (B.R.N i))) :=
    fun c => (c.1, cosetIn (rpI I u i c))
  have := ((l.ch u I.mu0).step i).fin_orb
  let chOf : (I.stp u I.mu0 i).Cl → Set.range φ := fun c => ⟨φ c, c, rfl⟩
  have key : ∀ c c', chOf c = chOf c' ↔ c.1 = c'.1 ∧ cosetIn (rpI I u i c) = cosetIn (rpI I u i c') := fun c c' =>
    Subtype.ext_iff.trans Prod.ext_iff
  have onto : Function.Surjective chOf := fun β => ⟨β.2.choose, Subtype.ext β.2.choose_spec⟩
  choose s hs using onto
  have hp : ∀ β c, chOf c = β ↔ c.1 = (s β).1 ∧ bar (rpI I u i c) = bar (rpI I u i (s β)) := fun β c => by
    rw [← cos_iff I hPr, ← key, hs]
  choose K K1 K2 K3 K4 K5 using fun β => chart_of I hI hP l Z u i hi (s β) (fun c => chOf c = β) (hp β)
  obtain ⟨k1, k2, k3⟩ := kStd_spec hPr u (B.R.N i)
  refine ⟨Set.range φ, Finite.of_surjective chOf fun β => ⟨_, hs β⟩, chOf, K, ⟨fun _ => kStd X u (B.R.N i),
    ⟨key, fun β => ⟨_, hs β⟩, fun β x => ?_, fun _ => k1, fun _ v hv _ _ => k2 v hv, fun _ => k3, fun c => ?_, fun c x q h => ?_,
      fun c x κ h1 h2 => ?_, fun c a => K5 _ _ _⟩⟩, fun c => K4 _ _, fun h => ?_⟩
  · exact (K1 β ▸ Iff.rfl : x ∈ (K β).lev.Lb ↔ x ∈ baseLb B.fields.E (B.R.N i) ((B.primes X).vT u)).trans (mem_baseLb hPr u _ x)
  · have e := K4 (chOf c) ⟨c, rfl⟩
    exact e ▸ yStd_spec I hI u i c
  · have e : ((K (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c := K4 (chOf c) ⟨c, rfl⟩
    replace h : PtOf (I.yStd u i c * x * kStd X u (B.R.N i)) q := e ▸ h
    have e2 := (K2 (chOf c)).trans (levU_congr I ((hp _ c).1 rfl).1 ((hp _ c).1 rfl).2).symm
    refine (e2 ▸ Iff.rfl : x ∈ (K (chOf c)).lev.U ↔ x ∈ levU B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs
      (chG (lvG I i c.1) (bar (rpI I u i c)))).trans ?_
    refine (lev_iff (X := B.fields) B.sp.cm I.twistPrimes_reference_tuple_eq_empty (lvG I i c.1) (lvQ I i c.1) (rpI I u i c) _
      (dia_of_pt hPr u (yStd_spec I hI u i c)).1 (dia_of_pt hPr u h).1 q (dia_of_pt hPr u (yStd_spec I hI u i c)).2
      (dia_of_pt hPr u h).2).trans ?_
    exact exists_congr fun κ => and_congr Iff.rfl (and_congr Iff.rfl (cos_iff I hPr _ _).symm)
  · have e : ((K (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c := K4 (chOf c) ⟨c, rfl⟩
    have hx : (id x.1 : GA B (B.R.N i)) ∈ levU (F := B.host.F) B.sp.cm (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs
      (chG (lvG I i (s (chOf c)).1) (bar (rpI I u i (s (chOf c))))) := K2 (chOf c) ▸ x.2
    refine (congrArg Units.val (K3 (chOf c) x hx)).trans ?_
    exact chr_congr I hPr hI c _ ((hp _ c).1 rfl).1 _ ⟨x.1, hx⟩ κ h1 (e ▸ h2)
  · have hm := B.R.two_le_m
    have hb : ∃ b : (I.stp u I.mu0 i).β, ∀ b', b' = b := by
      rcases h with rfl | rfl
      · obtain ⟨b, hb⟩ := (hI.idx_ok I.mu0).zero_uniq
        exact ⟨Idx.of b (by omega), fun b' => by rw [← hb (Idx.get b' (by omega)), Idx.of_get]⟩
      · exact ⟨_, fun b' => Idx.eq_top b' le_rfl⟩
    obtain ⟨b, hb⟩ := hb
    obtain ⟨q, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup I.mu0) (I.cst I.mu0) (u := u) (j := i) (DecoF.base _ _ _ _ _)
    refine ⟨⟨⟨chOf ((I.stp u I.mu0 i).cl b q)⟩, fun β => ?_⟩⟩
    rw [← hs β]
    exact (key _ _).2 ⟨hb _, cos_of_ne I (by omega) _ _⟩

end Main

end GlobalTheory.Mem.Col2.MemChart
end
end
