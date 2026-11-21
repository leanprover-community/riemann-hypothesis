import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.AnalyticForms.AnalyticCharts.ExistsAnalyticGraphChartMvPolynomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone

section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open MvPolynomial Module ReciprocityTheory.AnForm.R

theorem gbap_grad_rename {J : Type} [Fintype J] {n : ℕ} (e : J ≃ Fin n) (z₀ : J → ℂ)
    (f : MvPolynomial J ℤ) (j : Fin n) :
    grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e f)) j =
      eval z₀ (pderiv (e.symm j) (map (Int.castRingHom ℂ) f)) := by
  unfold grad
  have h := pderiv_rename (R := ℂ) e.injective (e.symm j) (map (Int.castRingHom ℂ) f)
  rw [Equiv.apply_symm_apply] at h
  have hc : (fun j => z₀ (e.symm j)) ∘ e = z₀ := by
    funext i
    simp
  rw [map_rename, h, eval_rename, hc]

theorem gbap_indep_grads {J : Type} [Fintype J] {D c : ℕ} (e : J ≃ Fin (D + 1 + c))
    (P : Ideal (MvPolynomial J ℤ)) (z₀ : J → ℂ) (T : Submodule ℂ (J → ℂ))
    (hT : ∀ w, w ∈ T ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsConeTangent (Int.castRingHom ℂ) P z₀ w)
    (hTd : finrank ℂ T = D + 1) :
    ∃ f : Fin c → MvPolynomial J ℤ, (∀ i, f i ∈ P) ∧
      LinearIndependent ℂ (fun i => grad (fun j => z₀ (e.symm j))
        (map (Int.castRingHom ℂ) (rename e (f i)))) := by
  classical
  let g : MvPolynomial J ℤ → (J → ℂ) := fun f i => eval z₀ (pderiv i (map (Int.castRingHom ℂ) f))
  obtain ⟨s, hsS, hspan, hsli⟩ := exists_linearIndependent ℂ (g '' (P : Set (MvPolynomial J ℤ)))
  have hfin : Finite s := hsli.finite
  haveI : Fintype s := Fintype.ofFinite s
  let ℓ : (J → ℂ) → (J → ℂ) →ₗ[ℂ] ℂ := fun w =>
    { toFun := fun v => ∑ i, v i * w i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.mul_sum, mul_assoc] }
  let A : Matrix s J ℂ := Matrix.of fun v i => (v : J → ℂ) i
  have hAli : LinearIndependent ℂ A.row := hsli
  have hker : ∀ w, w ∈ LinearMap.ker A.mulVecLin ↔ w ∈ T := by
    intro w
    rw [LinearMap.mem_ker, hT]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.IsConeTangent]
    constructor
    · intro hw f hf
      have hle : Submodule.span ℂ (s : Set (J → ℂ)) ≤ LinearMap.ker (ℓ w) := by
        rw [Submodule.span_le]
        intro v hv
        have := congrFun hw ⟨v, hv⟩
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, ℓ] using this
      have hg : g f ∈ Submodule.span ℂ (s : Set (J → ℂ)) := by
        rw [hspan]
        exact Submodule.subset_span ⟨f, hf, rfl⟩
      have := hle hg
      simpa [ℓ, g] using this
    · intro hw
      funext v
      obtain ⟨f, hf, hfv⟩ := hsS v.2
      have := hw f hf
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, Matrix.of_apply, Pi.zero_apply]
      rw [← hfv]
      simpa [g] using this
  have hkerT : LinearMap.ker A.mulVecLin = T := by
    ext w
    exact hker w
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrange : Module.finrank ℂ (LinearMap.range A.mulVecLin) = Fintype.card s := by
    have : A.rank = Fintype.card s := by
      rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hAli]
    exact this
  rw [hrange, hkerT, hTd, Module.finrank_fintype_fun_eq_card, Fintype.card_congr e,
    Fintype.card_fin] at hrn
  have hcard : Fintype.card s = c := by omega
  let σ : Fin c ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ i, ∃ f ∈ P, g f = (σ i : J → ℂ) := fun i => by
    obtain ⟨f, hf, hfv⟩ := hsS (σ i).2
    exact ⟨f, hf, hfv⟩
  choose f hfP hfg using hmem
  refine ⟨f, hfP, ?_⟩
  have hfam : (fun i => grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e (f i)))) =
      (LinearEquiv.funCongrLeft ℂ ℂ e.symm).toLinearMap ∘ (fun i => (σ i : J → ℂ)) := by
    funext i j
    rw [gbap_grad_rename]
    show g (f i) (e.symm j) = (σ i : J → ℂ) (e.symm j)
    rw [hfg i]
  rw [hfam]
  exact (hsli.comp σ σ.injective).map' _ (LinearEquiv.ker _)

theorem gbap_withBot_eq {x : WithBot ℕ∞} {d a : ℕ}
    (h : x + (a : WithBot ℕ∞) = ((d + a : ℕ) : WithBot ℕ∞)) : x = (d : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add] at h
    exact WithBot.bot_ne_coe h
  | coe y =>
    have h' : y + (a : ℕ∞) = ((d + a : ℕ) : ℕ∞) := by exact_mod_cast h
    have hy : y = (d : ℕ∞) := by
      induction y using ENat.recTopCoe with
      | top =>
        exfalso
        rw [top_add] at h'
        exact ENat.coe_ne_top _ h'.symm
      | coe y =>
        norm_cast at h' ⊢
        omega
    rw [hy]
    rfl

theorem gbap_van_map {R : Type*} [CommRing R] {n : ℕ} (φ : R →+* MvPolynomial (Fin n) ℂ)
    (I : Ideal R) (w : Fin n → ℂ) :
    (∀ g ∈ I.map φ, eval w g = 0) ↔ ∀ g ∈ I, eval w (φ g) = 0 := by
  constructor
  · intro h g hg
    exact h _ (Ideal.mem_map_of_mem φ hg)
  · intro h g hg
    have hle : I.map φ ≤ RingHom.ker (eval w) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact h x hx
    exact hle hg

theorem gbap_map_map_int {σ : Type*} (g : MvPolynomial σ ℤ) :
    map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℂ) g := by
  rw [map_map]
  congr 1

theorem gbap_surj_of_li {n c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (p : Fin n → ℂ)
    (hli : LinearIndependent ℂ (fun i => grad p (F i))) :
    Function.Surjective (fun v : Fin n → ℂ => fun i => ∑ j, eval p (pderiv j (F i)) * v j) := by
  let M : Matrix (Fin c) (Fin n) ℂ := Matrix.of fun i j => eval p (pderiv j (F i))
  have hli' : LinearIndependent ℂ M.row := hli
  have hrank : M.rank = c := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli', Fintype.card_fin]
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrank
  intro y
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop y
  exact ⟨v, by rw [← hv]; rfl⟩

theorem gbap_cut {J : Type} [Fintype J] {D c : ℕ} (e : J ≃ Fin (D + 1 + c))
    (P : Ideal (MvPolynomial J ℤ)) [P.IsPrime]
    (hhor : ∀ m : ℤ, (C m : MvPolynomial J ℤ) ∈ P → m = 0)
    (hdim : ringKrullDim (MvPolynomial J ℤ ⧸ P) = ((D + 1 + 1 : ℕ) : WithBot ℕ∞))
    (z₀ : J → ℂ) (hz₀ : ∀ f ∈ P, eval z₀ (map (Int.castRingHom ℂ) f) = 0)
    (f : Fin c → MvPolynomial J ℤ) (hfP : ∀ i, f i ∈ P)
    (hli : LinearIndependent ℂ
      (fun i => grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e (f i))))) :
    ∃ (F : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ) (h : MvPolynomial (Fin (D + 1 + c)) ℂ),
      LinearIndependent ℂ (fun i => grad (fun j => z₀ (e.symm j)) (F i)) ∧
      eval (fun j => z₀ (e.symm j)) h ≠ 0 ∧
      ∀ w : Fin (D + 1 + c) → ℂ, eval w h ≠ 0 →
        ((∀ i, eval w (F i) = 0) ↔
          ∀ g ∈ P, eval (fun j => w (e j)) (map (Int.castRingHom ℂ) g) = 0) := by
  classical
  set fe : MvPolynomial J ℤ ≃+* MvPolynomial (Fin (D + 1 + c)) ℤ :=
    (renameEquiv ℤ e).toRingEquiv with hfe
  have hfe_apply : ∀ g, (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) g = rename e g :=
    fun g => rfl
  have hfe_symm : ∀ g, fe.symm g = rename e.symm g := fun g => rfl
  set P' : Ideal (MvPolynomial (Fin (D + 1 + c)) ℤ) :=
    P.map (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) with hP'
  have hP'mem : ∀ g, g ∈ P' ↔ rename e.symm g ∈ P := by
    intro g
    rw [hP', Ideal.map_comap_of_equiv, Ideal.mem_comap]
    rfl
  haveI : P'.IsPrime := by
    rw [hP', Ideal.map_comap_of_equiv]
    infer_instance
  have hP'hor : ∀ m : ℤ, (C m : MvPolynomial (Fin (D + 1 + c)) ℤ) ∈ P' → m = 0 := by
    intro m hm
    rw [hP'mem, rename_C] at hm
    exact hhor m hm
  have hdim' : ringKrullDim (MvPolynomial (Fin (D + 1 + c)) ℤ ⧸ P') =
      ((D + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hdim]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P P' fe rfl)).symm
  obtain ⟨hQp, -, hQd⟩ := extQ_spec P' hP'hor
  haveI := hQp
  have hQdim : ringKrullDim (MvPolynomial (Fin (D + 1 + c)) ℚ ⧸ extQ P') =
      ((D + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim'] at hQd
    exact gbap_withBot_eq (a := 1) (by exact_mod_cast hQd)
  set K := extC (extQ P') with hK
  have hKvan : ∀ w : Fin (D + 1 + c) → ℂ, (∀ g ∈ K, eval w g = 0) ↔
      ∀ g ∈ P, eval (fun j => w (e j)) (map (Int.castRingHom ℂ) g) = 0 := by
    intro w
    rw [hK, extC, gbap_van_map, extQ]
    constructor
    · intro H g hg
      have := H _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) hg))
      rw [hfe_apply, gbap_map_map_int, map_rename, eval_rename] at this
      exact this
    · intro H g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        have hy' := (hP'mem y).1 hy
        have := H _ hy'
        rw [gbap_map_map_int]
        have hyy : y = rename e (rename e.symm y) := by
          rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
        rw [hyy, map_rename, eval_rename]
        exact this
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [smul_eq_mul, map_mul, map_mul, hx, mul_zero]
  set p' : Fin (D + 1 + c) → ℂ := fun j => z₀ (e.symm j) with hp'
  have hp'e : (fun j => p' (e j)) = z₀ := by
    funext j
    simp [hp']
  have hp'K : ∀ g ∈ K, eval p' g = 0 := by
    rw [hKvan, hp'e]
    exact hz₀
  have hKle : K ≤ ptIdeal p' := fun g hg => RingHom.mem_ker.2 (hp'K g hg)
  obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le hKle
  haveI : 𝔮.IsPrime := h𝔮min.1.1
  have hd𝔮 := ringKrullDim_of_mem_minimalPrimes_extC (extQ P') 𝔮 h𝔮min
  have hht := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field ℂ (D + 1 + c) 𝔮
  rw [hd𝔮, hQdim] at hht
  have hht' : (𝔮.height : WithBot ℕ∞) = (c : WithBot ℕ∞) :=
    gbap_withBot_eq (a := D + 1) (by rw [hht]; congr 1; omega)
  have hhtc : 𝔮.height ≤ c := by
    have : 𝔮.height = (c : ℕ∞) := by exact_mod_cast hht'
    rw [this]
  set F0 : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ :=
    fun i => map (Int.castRingHom ℂ) (rename e (f i)) with hF0
  have hF0K : ∀ i, F0 i ∈ K := by
    intro i
    have h1 : rename e (f i) ∈ P' :=
      Ideal.mem_map_of_mem (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) (hfP i)
    have := Ideal.mem_map_of_mem (map (algebraMap ℚ ℂ))
      (Ideal.mem_map_of_mem (map (Int.castRingHom ℚ)) h1)
    rw [gbap_map_map_int] at this
    exact this
  have hreg := isRegularLocalRing_of_jacobian K p' hp'K F0 hF0K hli ⟨𝔮, h𝔮min, h𝔮le, hhtc⟩
  haveI := hreg.1
  have hcc : D + 1 + c - (D + 1) = c := by omega
  obtain ⟨-, F', hF'K, hF'li, h, hh, hspan⟩ :=
    exists_jacobian_cut K p' (D + 1) (by rw [hreg.2]; congr 2; omega)
  refine ⟨fun i => F' (Fin.cast hcc.symm i), h, ?_, hh, ?_⟩
  · exact hF'li.comp _ (Fin.cast_injective _)
  · intro w hw
    rw [← hKvan]
    constructor
    · intro H g hg
      have hsp : Ideal.span (Set.range F') ≤ RingHom.ker (eval w) := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        have := H (Fin.cast hcc j)
        simp only [Fin.cast_cast, Fin.cast_eq_self] at this
        exact RingHom.mem_ker.2 this
      have := RingHom.mem_ker.1 (hsp (hspan g hg))
      rw [map_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hw
    · intro H i
      exact H _ (hF'K _)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem gbap_analyticAt_apply {n : Type} [Fintype n] (j : n) (z : n → ℂ) :
    AnalyticAt ℂ (fun z : n → ℂ => z j) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).analyticAt z

theorem gbap_insertNth_eq {D : ℕ} (k : Fin (D + 1)) (a : ℂ) (b : Fin D → ℂ) (w : Fin (D + 1) → ℂ)
    (hk : w k = a) (hb : ∀ i, w (k.succAbove i) = b i) : Fin.insertNth k a b = w := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
  · simp [hk]
  · simp [hb]

theorem gbap_param_of_cut {D c : ℕ} (Z : Set (Fin (D + 1 + c) → ℂ))
    (hZc : ∀ z ∈ Z, ∀ t : ℂ, t ≠ 0 → t • z ∈ Z)
    (F : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ) (h : MvPolynomial (Fin (D + 1 + c)) ℂ)
    (hZ : ∀ z, z ≠ 0 → eval z h ≠ 0 → (z ∈ Z ↔ ∀ i, eval z (F i) = 0))
    (p : Fin (D + 1 + c) → ℂ) (hp : p ∈ Z) (hp0 : p ≠ 0) (hph : eval p h ≠ 0)
    (hjac : Function.Surjective (fun v : Fin (D + 1 + c) → ℂ =>
      fun i => ∑ j, eval p (pderiv j (F i)) * v j)) :
    ∃ (ρ₀ : ℝ) (γ : (Fin D → ℂ) → Fin (D + 1 + c) → ℂ), 0 < ρ₀ ∧
      AnalyticOnNhd ℂ γ (Metric.ball 0 ρ₀) ∧ (∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, γ y ∈ Z) ∧
      (∃ (O : Set (Fin (D + 1 + c) → ℂ)) (q : (Fin (D + 1 + c) → ℂ) → Fin D → ℂ), IsOpen O ∧
        AnalyticOnNhd ℂ q O ∧ O ∩ Z = coneOver (Metric.ball 0 ρ₀) γ ∧
        (∀ z ∈ O, ∀ t : ℂ, t ≠ 0 → t • z ∈ O ∧ q (t • z) = q z) ∧
        ∀ y ∈ Metric.ball 0 ρ₀, q (γ y) = y) ∧ γ 0 = p := by
  classical
  have hF0 : ∀ i, eval p (F i) = 0 := (hZ p hp0 hph).1 hp
  obtain ⟨σ, U, V, g, hU, hpU, hV, hg, hbij, hproj⟩ :=
    ReciprocityTheory.AnForm.exists_analytic_graph_chart_mvPolynomial F p hF0 hjac
  obtain ⟨π, hπ⟩ : ∃ π : (Fin (D + 1 + c) → ℂ) → Fin (D + 1) → ℂ,
      π = fun z i => z (σ (Fin.castAdd c i)) := ⟨_, rfl⟩
  have hπa : ∀ z i, π z i = z (σ (Fin.castAdd c i)) := fun z i => by rw [hπ]
  have hπs : ∀ (t : ℂ) z, π (t • z) = t • π z := fun t z => by
    funext i
    simp [hπa]
  have hπg : ∀ w ∈ V, π (g w) = w := fun w hw => by
    rw [hπ]
    exact hproj w hw
  have hπan : ∀ j z, AnalyticAt ℂ (fun z => π z j) z := fun j z => by
    rw [hπ]
    exact gbap_analyticAt_apply _ z
  have htgt : ∀ z, z ≠ 0 → z ∈ Z → z ∈ U → eval z h ≠ 0 → ∃ w ∈ V, g w = z ∧ w = π z := by
    intro z hz0 hzZ hzU hzh
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hzU, (hZ z hz0 hzh).1 hzZ⟩
    exact ⟨w, hw, hgw, by rw [← hgw, hπg w hw]⟩
  obtain ⟨w₀, hw₀V, hgw₀, hw₀⟩ := htgt p hp0 hp hpU hph
  have hπp : π p ≠ 0 := by
    intro hπ0
    have hWo : IsOpen (U ∩ {z | eval z h ≠ 0} ∩ {z | z ≠ 0}) :=
      (hU.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)).inter
        isOpen_ne
    have hc : ContinuousAt (fun t : ℂ => t • p) 1 :=
      (continuous_id.smul continuous_const).continuousAt
    have hev : ∀ᶠ t in nhds (1 : ℂ), t • p ∈ U ∩ {z | eval z h ≠ 0} ∩ {z | z ≠ 0} :=
      hc.preimage_mem_nhds (by rw [one_smul]; exact hWo.mem_nhds ⟨⟨hpU, hph⟩, hp0⟩)
    obtain ⟨t, ⟨⟨htU, hth⟩, htp0⟩, ht1⟩ :=
      ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := ({1}ᶜ : Set ℂ)))).exists
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact htp0 (zero_smul ℂ p)
    obtain ⟨w, hwV, hgw, hw⟩ := htgt (t • p) htp0 (hZc p hp t ht0) htU hth
    have hw0 : w = w₀ := by
      rw [hw, hw₀, hπs, hπ0, smul_zero]
    have htp : t • p = p := by rw [← hgw, hw0, hgw₀]
    have : (t - 1) • p = 0 := by rw [sub_smul, one_smul, htp, sub_self]
    rcases smul_eq_zero.1 this with h1 | h1
    · exact ht1 (sub_eq_zero.1 h1)
    · exact hp0 h1
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hπp
  set a := π p k with ha_def
  have ha : a ≠ 0 := hk
  obtain ⟨W, hW⟩ : ∃ W : (Fin D → ℂ) → Fin (D + 1) → ℂ,
      W = fun y => Fin.insertNth k a (fun i => π p (k.succAbove i) + y i) := ⟨_, rfl⟩
  have hWk : ∀ y, W y k = a := fun y => by rw [hW]; simp
  have hWs : ∀ y i, W y (k.succAbove i) = π p (k.succAbove i) + y i := fun y i => by
    rw [hW]; simp
  have hW0 : W 0 = π p := by
    rw [hW]
    exact gbap_insertNth_eq k a _ (π p) rfl (fun i => by simp)
  have hWan : ∀ y, AnalyticAt ℂ W y := by
    intro y
    rw [hW]
    refine analyticAt_pi_iff.2 fun j => ?_
    rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
    · simp only [Fin.insertNth_apply_same]
      exact analyticAt_const
    · simp only [Fin.insertNth_apply_succAbove]
      exact analyticAt_const.add (gbap_analyticAt_apply i y)
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun y => (hWan y).continuousAt
  have hGo : IsOpen (V ∩ g ⁻¹' {z | eval z h ≠ 0}) :=
    hg.continuousOn.isOpen_inter_preimage hV
      (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)
  have h0G : (0 : Fin D → ℂ) ∈ W ⁻¹' (V ∩ g ⁻¹' {z | eval z h ≠ 0}) := by
    simp only [Set.mem_preimage, Set.mem_inter_iff, hW0, ← hw₀]
    exact ⟨hw₀V, by rw [Set.mem_ofPred_eq, hgw₀]; exact hph⟩
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 (hGo.preimage hWc) 0 h0G
  have hyV : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, W y ∈ V ∧ eval (g (W y)) h ≠ 0 :=
    fun y hy => hball hy
  have hγmem : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀,
      g (W y) ∈ U ∧ ∀ i, eval (g (W y)) (F i) = 0 := fun y hy => hbij.mapsTo (hyV y hy).1
  have hπγ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, π (g (W y)) = W y := fun y hy =>
    hπg _ (hyV y hy).1
  have hγ0 : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, g (W y) ≠ 0 := by
    intro y hy h0
    have := congrFun (hπγ y hy) k
    rw [h0, hWk, hπa] at this
    exact ha (by simpa using this.symm)
  have hγZ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, g (W y) ∈ Z := fun y hy =>
    (hZ _ (hγ0 y hy) (hyV y hy).2).2 (hγmem y hy).2
  obtain ⟨q, hq⟩ : ∃ q : (Fin (D + 1 + c) → ℂ) → Fin D → ℂ,
      q = fun z i => π z (k.succAbove i) * a / π z k - π p (k.succAbove i) := ⟨_, rfl⟩
  have hqa : ∀ z i, q z i = π z (k.succAbove i) * a / π z k - π p (k.succAbove i) :=
    fun z i => by rw [hq]
  obtain ⟨ν, hν⟩ : ∃ ν : (Fin (D + 1 + c) → ℂ) → Fin (D + 1 + c) → ℂ,
      ν = fun z => (a / π z k) • z := ⟨_, rfl⟩
  have hνa : ∀ z, ν z = (a / π z k) • z := fun z => by rw [hν]
  set A : Set (Fin (D + 1 + c) → ℂ) := {z | π z k ≠ 0} with hA
  have hAo : IsOpen A :=
    isOpen_ne_fun (continuous_iff_continuousAt.2 fun z => (hπan k z).continuousAt) continuous_const
  have hqan : ∀ z ∈ A, AnalyticAt ℂ q z := by
    intro z hz
    rw [hq]
    refine analyticAt_pi_iff.2 fun i => ?_
    exact (((hπan _ z).mul analyticAt_const).div (hπan k z) hz).sub analyticAt_const
  have hνan : ∀ z ∈ A, AnalyticAt ℂ ν z := by
    intro z hz
    rw [hν]
    refine analyticAt_pi_iff.2 fun j => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (analyticAt_const.div (hπan k z) hz).mul (gbap_analyticAt_apply j z)
  set O : Set (Fin (D + 1 + c) → ℂ) :=
    A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0}) ∩ q ⁻¹' Metric.ball 0 ρ₀ with hO
  have hOo : IsOpen O := by
    have h1 : IsOpen (A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0})) :=
      ContinuousOn.isOpen_inter_preimage (show ContinuousOn ν A from fun z hz => (hνan z hz).continuousAt.continuousWithinAt)
        hAo (hU.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const))
    exact ContinuousOn.isOpen_inter_preimage (show ContinuousOn q (A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0})) from
      fun z hz => (hqan z hz.1).continuousAt.continuousWithinAt) h1
      Metric.isOpen_ball
  have hπks : ∀ z (t : ℂ), π (t • z) k = t * π z k := fun z t => by rw [hπs]; rfl
  have hνs : ∀ z (t : ℂ), t ≠ 0 → π z k ≠ 0 → ν (t • z) = ν z := by
    intro z t ht hz
    rw [hνa, hνa, hπks, smul_smul]
    congr 1
    field_simp
  have hqs : ∀ z (t : ℂ), t ≠ 0 → π z k ≠ 0 → q (t • z) = q z := by
    intro z t ht hz
    funext i
    rw [hqa, hqa, hπs]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  have hqγ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, q (g (W y)) = y := by
    intro y hy
    funext i
    rw [hqa, hπγ y hy, hWk, hWs]
    field_simp
    ring
  refine ⟨ρ₀, fun y => g (W y), hρ₀, ?_, hγZ, ⟨O, q, hOo, fun z hz => hqan z hz.1.1, ?_, ?_, hqγ⟩, ?_⟩
  · intro y hy
    exact (hg _ (hyV y hy).1).comp (hWan y)
  · ext z
    constructor
    · rintro ⟨⟨⟨hzA, hzU, hzh⟩, hzq⟩, hzZ⟩
      have hzA' : π z k ≠ 0 := hzA
      have hc : a / π z k ≠ 0 := div_ne_zero ha hzA'
      have hνZ : ν z ∈ Z := by rw [hνa]; exact hZc z hzZ _ hc
      have hν0 : ν z ≠ 0 := by
        intro h0
        have := hπks z (a / π z k)
        rw [← hνa, h0] at this
        rw [hπa] at this
        simp only [Pi.zero_apply] at this
        field_simp at this
        exact ha this.symm
      obtain ⟨w, hwV, hgw, hw⟩ := htgt (ν z) hν0 hνZ hzU hzh
      have hWq : W (q z) = π (ν z) := by
        rw [hW]
        apply gbap_insertNth_eq
        · rw [hνa, hπks]
          field_simp
        · intro i
          rw [hνa, hπs, hqa]
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
      refine ⟨q z, hzq, π z k / a, div_ne_zero hzA' ha, ?_⟩
      simp only
      rw [hWq, ← hw, hgw, hνa, smul_smul]
      rw [div_mul_div_comm, mul_comm (π z k) a, div_self (mul_ne_zero ha hzA'), one_smul]
    · rintro ⟨y, hy, t, ht, rfl⟩
      have hwk : π (g (W y)) k = a := by rw [hπγ y hy, hWk]
      have hwk0 : π (g (W y)) k ≠ 0 := by rw [hwk]; exact ha
      have hνw : ν (t • g (W y)) = g (W y) := by
        rw [hνs _ _ ht hwk0, hνa, hwk, div_self ha, one_smul]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hZc _ (hγZ y hy) t ht⟩
      · show π (t • g (W y)) k ≠ 0
        rw [hπks]
        exact mul_ne_zero ht hwk0
      · simp only [Set.mem_preimage, hνw]
        exact ⟨(hγmem y hy).1, (hyV y hy).2⟩
      · simp only [Set.mem_preimage]
        rw [hqs _ _ ht hwk0, hqγ y hy]
        exact hy
  · intro z hz t ht
    have hzA : π z k ≠ 0 := hz.1.1
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hqs z t ht hzA⟩
    · show π (t • z) k ≠ 0
      rw [hπks]
      exact mul_ne_zero ht hzA
    · simp only [Set.mem_preimage]
      rw [hνs z t ht hzA]
      exact hz.1.2
    · simp only [Set.mem_preimage]
      rw [hqs z t ht hzA]
      exact hz.2
  · simp only
    rw [hW0, ← hw₀, hgw₀]

section Pts

variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem gbap_eval_smul {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (c : ℂ) (z : ι → ℂ) :
    eval (c • z) φ = c ^ n * eval z φ := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hφ.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hs : d.degree = ∑ i ∈ d.support, d i := rfl
  rw [← hdeg, hs]
  ring

theorem gbap_smul_mem_pts {J : Type} [Fintype J] (x : J → Ω) {z : J → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) {c : ℂ} (hc : c ≠ 0) : c • z ∈ pts (coordIdeal ℤ x) := by
  refine ⟨smul_ne_zero hc hz.1, fun f hf => ?_⟩
  have hH := coordIdeal_isHomogIdeal ℤ x
  rw [← sum_homogeneousComponent f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [gbap_eval_smul ((homogeneousComponent_isHomogeneous d f).map _),
    hz.2 _ (hH f hf d), mul_zero]


end Pts

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem gaap_measurableSet_pts {J : Type} [Fintype J] (P : Ideal (MvPolynomial J ℤ)) :
    MeasurableSet (pts P) := by
  have : pts P = ({0}ᶜ : Set (J → ℂ)) ∩
      ⋂ f ∈ P, {z : J → ℂ | eval z (map (Int.castRingHom ℂ) f) = 0} := by
    ext z
    simp [pts, conePts]
  rw [this]
  refine (measurableSet_singleton 0).compl.inter (IsClosed.measurableSet ?_)
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const

theorem gaap_mem_ball_add {y₀ y : Fin D → ℂ} {ρ₀ : ℝ} :
    y₀ + y ∈ Metric.ball y₀ ρ₀ ↔ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀ := by
  simp [Metric.mem_ball, dist_eq_norm]

theorem exists_isParam {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {z₀ : Ix κ → ℂ} (hz₀ : z₀ ∈ pts (coordIdeal ℤ x)) :
    ∃ (ρ₀ : ℝ) (γ : (Fin D → ℂ) → Ix κ → ℂ), 0 < ρ₀ ∧
      IsParam (coordIdeal ℤ x) (Metric.ball 0 ρ₀) γ ∧ γ 0 = z₀ := by
  classical
  set P := coordIdeal ℤ x with hPdef
  obtain ⟨T, hT, hTd⟩ := hg.smooth z₀ hz₀
  obtain ⟨-, ⟨hprime, -, -⟩, hhor, hdim⟩ := hg.arith
  haveI : P.IsPrime := hprime
  have hTle : D + 1 ≤ Fintype.card (Ix κ) := by
    rw [← hTd, ← Module.finrank_fintype_fun_eq_card ℂ]
    exact Submodule.finrank_le T
  set c := Fintype.card (Ix κ) - (D + 1) with hc
  let e : Ix κ ≃ Fin (D + 1 + c) := Fintype.equivFinOfCardEq (by omega)
  have hhor' : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ P → m = 0 := by
    intro m hm
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial (Ix κ) ℤ) := hm
    rw [hhor] at this
    exact (Submodule.mem_bot ℤ).1 this
  have hdim' : ringKrullDim (MvPolynomial (Ix κ) ℤ ⧸ P) = ((D + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    convert hdim using 3
    simp
  obtain ⟨f, hfP, hli⟩ := gbap_indep_grads e P z₀ T hT hTd
  obtain ⟨F, h, hFli, hph, hiff⟩ := gbap_cut e P hhor' hdim' z₀ hz₀.2 f hfP hli
  set p' : Fin (D + 1 + c) → ℂ := fun j => z₀ (e.symm j) with hp'
  set Z' : Set (Fin (D + 1 + c) → ℂ) := {w | (fun j => w (e j)) ∈ pts P} with hZ'
  have hψ0 : ∀ w : Fin (D + 1 + c) → ℂ, w ≠ 0 → (fun j => w (e j)) ≠ 0 := by
    intro w hw h0
    apply hw
    funext i
    have := congrFun h0 (e.symm i)
    simpa using this
  have hZc : ∀ w ∈ Z', ∀ t : ℂ, t ≠ 0 → t • w ∈ Z' := by
    intro w hw t ht
    exact gbap_smul_mem_pts x hw ht
  have hZ : ∀ w, w ≠ 0 → eval w h ≠ 0 → (w ∈ Z' ↔ ∀ i, eval w (F i) = 0) := by
    intro w hw hwh
    rw [hiff w hwh]
    exact ⟨fun H => H.2, fun H => ⟨hψ0 w hw, H⟩⟩
  have hp'e : (fun j => p' (e j)) = z₀ := by
    funext j
    simp [hp']
  have hp'Z : p' ∈ Z' := by
    show (fun j => p' (e j)) ∈ pts P
    rw [hp'e]
    exact hz₀
  have hp'0 : p' ≠ 0 := by
    intro h0
    apply hz₀.1
    rw [← hp'e, h0]
    rfl
  obtain ⟨ρ₀, γ', hρ₀, hγan, hγZ, ⟨O', q', hO', hq', hOeq, hOc, hqγ⟩, hγ0⟩ :=
    gbap_param_of_cut Z' hZc F h hZ p' hp'Z hp'0 hph (gbap_surj_of_li F p' hFli)
  refine ⟨ρ₀, fun y j => γ' y (e j), hρ₀, ⟨Metric.isOpen_ball, ?_, fun y hy => hγZ y hy,
    {z | (fun i => z (e.symm i)) ∈ O'}, fun z => q' (fun i => z (e.symm i)), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    exact analyticAt_pi_iff.2 fun j => (gbap_analyticAt_apply (e j) _).comp (hγan y hy)
  · exact hO'.preimage (continuous_pi fun i => continuous_apply _)
  · intro z hz
    exact (hq' _ hz).comp (analyticAt_pi_iff.2 fun i => gbap_analyticAt_apply (e.symm i) z)
  · ext z
    have hzz : (fun j => (fun i => z (e.symm i)) (e j)) = z := by
      funext j
      simp
    constructor
    · rintro ⟨hzO, hzP⟩
      have : (fun i => z (e.symm i)) ∈ O' ∩ Z' := ⟨hzO, by
        show _ ∈ pts P
        rw [hzz]
        exact hzP⟩
      rw [hOeq] at this
      obtain ⟨y, hy, t, ht, hte⟩ := this
      refine ⟨y, hy, t, ht, ?_⟩
      funext j
      have := congrFun hte (e j)
      simpa using this
    · rintro ⟨y, hy, t, ht, rfl⟩
      have hmem : t • γ' y ∈ O' ∩ Z' := by
        rw [hOeq]
        exact ⟨y, hy, t, ht, rfl⟩
      have heq : (fun i => (t • fun j => γ' y (e j)) (e.symm i)) = t • γ' y := by
        funext i
        simp
      refine ⟨?_, ?_⟩
      · show (fun i => (t • fun j => γ' y (e j)) (e.symm i)) ∈ O'
        rw [heq]
        exact hmem.1
      · exact hmem.2
  · intro z hz t ht
    exact hOc _ hz t ht
  · intro y hy
    have : (fun i => γ' y (e (e.symm i))) = γ' y := by
      funext i
      simp
    show q' (fun i => γ' y (e (e.symm i))) = y
    rw [this]
    exact hqγ y hy
  · funext j
    show γ' 0 (e j) = z₀ j
    rw [hγ0]
    simp [hp']

theorem IsParam.translate {P : Ideal (MvPolynomial (Ix κ) ℤ)} {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → Ix κ → ℂ} (h : IsParam P U γ) (y₀ : Fin D → ℂ) {ρ₀ : ℝ}
    (hball : Metric.ball y₀ ρ₀ ⊆ U) :
    IsParam P (Metric.ball 0 ρ₀) fun y => γ (y₀ + y) := by
  obtain ⟨_, hd, hpts, O, q, hO, hq, hOeq, hsc, hqγ⟩ := h
  have hmaps : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, y₀ + y ∈ U := fun y hy =>
    hball (gaap_mem_ball_add.2 hy)
  have hγO : ∀ y ∈ U, γ y ∈ O := fun y hy => by
    have : γ y ∈ coneOver U γ := ⟨y, hy, 1, one_ne_zero, (one_smul ℂ _).symm⟩
    rw [← hOeq] at this
    exact this.1
  refine ⟨Metric.isOpen_ball, ?_, fun y hy => hpts _ (hmaps y hy),
    O ∩ q ⁻¹' Metric.ball y₀ ρ₀, fun z => q z - y₀,
    hq.continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball,
    (hq.mono Set.inter_subset_left).sub analyticOnNhd_const, ?_, ?_, ?_⟩
  · exact hd.comp (analyticOnNhd_const.add analyticOnNhd_id) fun y hy => hmaps y hy
  · ext z
    constructor
    · rintro ⟨⟨hzO, hzq⟩, hzp⟩
      have hz : z ∈ coneOver U γ := hOeq ▸ ⟨hzO, hzp⟩
      obtain ⟨y, hyU, c, hc, rfl⟩ := hz
      have h1 : q (c • γ y) = y := by rw [(hsc _ (hγO y hyU) c hc).2, hqγ y hyU]
      have hy : y ∈ Metric.ball y₀ ρ₀ := by
        have := hzq
        simp only [Set.mem_preimage, h1] at this
        exact this
      refine ⟨y - y₀, ?_, c, hc, ?_⟩
      · rw [← gaap_mem_ball_add (y₀ := y₀), add_sub_cancel]
        exact hy
      · simp
    · rintro ⟨y, hy, c, hc, rfl⟩
      have hcone : c • γ (y₀ + y) ∈ coneOver U γ := ⟨y₀ + y, hmaps y hy, c, hc, rfl⟩
      rw [← hOeq] at hcone
      refine ⟨⟨hcone.1, ?_⟩, hcone.2⟩
      simp only [Set.mem_preimage]
      rw [(hsc _ (hγO _ (hmaps y hy)) c hc).2, hqγ _ (hmaps y hy)]
      exact gaap_mem_ball_add.2 hy
  · rintro z ⟨hzO, hzq⟩ c hc
    have := hsc z hzO c hc
    refine ⟨⟨this.1, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, this.2]
      exact hzq
    · simp only [this.2]
  · intro y hy
    simp only
    rw [hqγ _ (hmaps y hy), add_sub_cancel_left]

theorem gaap_setLIntegral_translate (y₀ : Fin D → ℂ) (ρ₀ : ℝ) (F : (Fin D → ℂ) → ENNReal) :
    ∫⁻ y in Metric.ball (0 : Fin D → ℂ) ρ₀, F (y₀ + y) = ∫⁻ y in Metric.ball y₀ ρ₀, F y := by
  have hpre : (fun y => y₀ + y) ⁻¹' Metric.ball y₀ ρ₀ = Metric.ball (0 : Fin D → ℂ) ρ₀ := by
    ext y
    exact gaap_mem_ball_add
  rw [← hpre]
  exact (measurePreserving_add_left volume y₀).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft y₀) F _

theorem IsDensityFor.translate {P : Ideal (MvPolynomial (Ix κ) ℤ)} {μ : Measure (Ix κ → ℂ)}
    {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) (y₀ : Fin D → ℂ) {ρ₀ : ℝ} (hball : Metric.ball y₀ ρ₀ ⊆ U) :
    IsDensityFor μ (Metric.ball 0 ρ₀) (fun y => γ (y₀ + y)) fun y => ν (y₀ + y) := by
  obtain ⟨hνc, hνpos, hνint⟩ := hν
  have hmaps : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, y₀ + y ∈ U := fun y hy =>
    hball (gaap_mem_ball_add.2 hy)
  refine ⟨hνc.comp (contDiffOn_const.add contDiffOn_id) (fun y hy => hmaps y hy),
    fun y hy => hνpos _ (hmaps y hy), ?_⟩
  intro g hg hg0 hgnn
  obtain ⟨_, _, _, O', q', hO', -, hO'eq, -, -⟩ := h.translate y₀ hball
  obtain ⟨hU, _, _, O, q, _, _, hOeq, hsc, hqγ⟩ := h
  have hγO : ∀ y ∈ U, γ y ∈ O := fun y hy => by
    have : γ y ∈ coneOver U γ := ⟨y, hy, 1, one_ne_zero, (one_smul ℂ _).symm⟩
    rw [← hOeq] at this
    exact this.1
  set S := coneOver (Metric.ball (0 : Fin D → ℂ) ρ₀) (fun y => γ (y₀ + y)) with hSdef
  have hSm : MeasurableSet S := by
    rw [← hO'eq]
    exact hO'.measurableSet.inter (gaap_measurableSet_pts P)
  have hSsub : S ⊆ coneOver U γ := by
    rintro z ⟨y, hy, c, hc, rfl⟩
    exact ⟨y₀ + y, hmaps y hy, c, hc, rfl⟩
  have hSsmul : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → (c • z ∈ S ↔ z ∈ S) := by
    intro c z hc
    constructor
    · rintro ⟨y, hy, c', hc', he⟩
      refine ⟨y, hy, c⁻¹ * c', mul_ne_zero (inv_ne_zero hc) hc', ?_⟩
      rw [mul_smul, ← he, smul_smul, inv_mul_cancel₀ hc, one_smul]
    · rintro ⟨y, hy, c', hc', rfl⟩
      exact ⟨y, hy, c * c', mul_ne_zero hc hc', by rw [mul_smul]⟩
  have hγS : ∀ y ∈ U, (γ y ∈ S ↔ y ∈ Metric.ball y₀ ρ₀) := by
    intro y hyU
    constructor
    · rintro ⟨y', hy', c, hc, he⟩
      have h1 : q (γ y) = y₀ + y' := by
        rw [he, (hsc _ (hγO _ (hmaps y' hy')) c hc).2, hqγ _ (hmaps y' hy')]
      rw [hqγ y hyU] at h1
      rw [h1]
      exact gaap_mem_ball_add.2 hy'
    · intro hy
      refine ⟨y - y₀, ?_, 1, one_ne_zero, ?_⟩
      · rw [← gaap_mem_ball_add (y₀ := y₀), add_sub_cancel]
        exact hy
      · simp
  have key := hνint (S.indicator g) (hg.indicator hSm)
    (fun c z hc => by
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hSsmul c z hc).2 hz), hg0 c z hc]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz ((hSsmul c z hc).1 h'))])
    (fun z => Set.indicator_nonneg (fun z _ => hgnn z) z)
  have hL : ∫⁻ z in coneOver U γ, ENNReal.ofReal (S.indicator g z) ∂μ =
      ∫⁻ z in S, ENNReal.ofReal (g z) ∂μ := by
    have : (fun z => ENNReal.ofReal (S.indicator g z)) = S.indicator (fun z => ENNReal.ofReal (g z)) := by
      funext z
      by_cases hz : z ∈ S <;> simp [hz]
    rw [this, setLIntegral_indicator hSm, Set.inter_eq_left.2 hSsub]
  have hR : ∫⁻ y in U, ENNReal.ofReal (S.indicator g (γ y) * ν y) =
      ∫⁻ y in Metric.ball y₀ ρ₀, ENNReal.ofReal (g (γ y) * ν y) := by
    rw [← Set.inter_eq_left.2 hball, ← setLIntegral_indicator Metric.isOpen_ball.measurableSet]
    refine setLIntegral_congr_fun hU.measurableSet (fun y hyU => ?_)
    by_cases hy : y ∈ Metric.ball y₀ ρ₀
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hγS y hyU).2 hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h' => hy ((hγS y hyU).1 h'))]
      simp
  rw [← hL, key, hR]
  exact (gaap_setLIntegral_translate y₀ ρ₀ (fun y => ENNReal.ofReal (g (γ y) * ν y))).symm


end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
