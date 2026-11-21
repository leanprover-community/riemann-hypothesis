import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundaryStatement

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.PolarMultilinear

theorem powerset_map {α β : Type} (f : α → β) (s : Multiset α) :
    (s.map f).powerset = s.powerset.map (Multiset.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.powerset_cons, ih, Multiset.map_map]

theorem powerset_val {α : Type} (s : Finset α) :
    s.val.powerset = s.powerset.val.map Finset.val := by
  simp [Finset.powerset, Multiset.map_pmap, Multiset.pmap_eq_map]

theorem alt_sum {d : ℕ} (r : Fin d → Fin d) :
    (∑ T : Finset (Fin d), if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) =
      if Function.Surjective r then 1 else 0 := by
  classical
  have h := Finset.prod_add (fun _ : Fin d => (1 : ℝ))
    (fun j : Fin d => if j ∈ Set.range r then (0 : ℝ) else -1) Finset.univ
  rw [Finset.powerset_univ] at h
  have h2 : ∀ T : Finset (Fin d), (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) =
      (∏ _i ∈ T, (1 : ℝ)) * ∏ j ∈ Finset.univ \ T, (if j ∈ Set.range r then (0 : ℝ) else -1) := by
    intro T
    rw [Finset.prod_const_one, one_mul]
    split_ifs with hT
    · rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℝ)), Finset.prod_const, Finset.card_univ_diff,
        Fintype.card_fin]
      intro j hj
      rw [if_neg]
      rintro ⟨i, rfl⟩
      exact (Finset.mem_sdiff.1 hj).2 (hT i)
    · obtain ⟨i, hi⟩ := not_forall.1 hT
      exact (Finset.prod_eq_zero (i := r i) (by simp [hi]) (by simp)).symm
  rw [Finset.sum_congr rfl fun T _ => h2 T, ← h]
  split_ifs with hs
  · refine Finset.prod_eq_one fun j _ => ?_
    rw [if_pos (show j ∈ Set.range r from hs j), add_zero]
  · obtain ⟨j, hj⟩ := not_forall.1 hs
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [if_neg (show ¬ j ∈ Set.range r from hj)]; ring

theorem alt_sum_multilinear {A : Type} [AddCommGroup A] {d : ℕ}
    (M : MultilinearMap ℤ (fun _ : Fin d => A) ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin d)) (a : Fin d → A), M (a ∘ σ) = M a) (a : Fin d → A) :
    (∑ T : Finset (Fin d), (-1 : ℝ) ^ (d - T.card) * M fun _ => ∑ i ∈ T, a i) =
      (d.factorial : ℝ) * M a := by
  classical
  have h1 : ∀ T : Finset (Fin d), (-1 : ℝ) ^ (d - T.card) * (M fun _ => ∑ i ∈ T, a i) =
      ∑ r : Fin d → Fin d, (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) * M (a ∘ r) := by
    intro T
    rw [M.map_sum_finset (fun _ i => a i) (fun _ => T), Finset.mul_sum]
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun r _ => rfl
    ext r
    simp [Fintype.mem_piFinset]
  rw [Finset.sum_congr rfl fun T _ => h1 T, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, alt_sum, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have h3 : (∑ r ∈ Finset.univ.filter (fun r : Fin d → Fin d => Function.Surjective r), M (a ∘ r)) =
      ∑ σ : Equiv.Perm (Fin d), M (a ∘ σ) := by
    symm
    refine Finset.sum_bij (fun σ _ => (σ : Fin d → Fin d)) ?_ ?_ ?_ ?_
    · intro σ _
      simpa using σ.surjective
    · intro σ _ τ _ h
      exact Equiv.ext (congrFun h)
    · intro r hr
      have hs : Function.Surjective r := by simpa using hr
      exact ⟨Equiv.ofBijective r (Finite.surjective_iff_bijective.1 hs), Finset.mem_univ _, rfl⟩
    · intro σ _
      rfl
  rw [h3]
  simp [hM, Fintype.card_perm]

theorem polar_diag : ∀ (A : Type) [AddCommGroup A] (d : ℕ) (M : MultilinearMap ℤ (fun _ : Fin d => A) ℝ),
    (∀ (σ : Equiv.Perm (Fin d)) (a : Fin d → A), M (a ∘ σ) = M a) →
    ∀ a : Fin d → A, polar (fun b => M fun _ => b) (Multiset.map a Finset.univ.val) = M a := by
  intro A _ d M hM a
  have hc : Multiset.card (Multiset.map a Finset.univ.val) = d := by simp
  unfold Pad.polar
  rw [hc, powerset_map, powerset_val, Multiset.map_map, Multiset.map_map, Finset.powerset_univ]
  have h := alt_sum_multilinear M hM a
  have h' : (Multiset.map (((fun T : Multiset A => (-1 : ℝ) ^ (d - Multiset.card T) * M fun _ => T.sum) ∘
      Multiset.map a) ∘ Finset.val) (Finset.univ : Finset (Finset (Fin d))).val).sum =
      (d.factorial : ℝ) * M a := by
    rw [← h, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun T _ => ?_
    simp only [Function.comp, Multiset.card_map, Finset.card_val]
    rfl
  rw [h', ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]

end GlobalTheory.ShFam.PolarMultilinear
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_presenting_divisor : HTBoundSt → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag), AdmEx S κ → ∀ (k : s.Comp) (w : Sym D.host.E →₀ ℤ), (∀ a ∈ w.support, {q | a.1 q = true}.Finite) → ∃ (M : GlobalTheory.TrueGeo.Model (fl.C k).Y) (L : LB M.X) (m : ℕ+) (r : (L.pull M.j).ι → (fl.C k).Y.Fnˣ), L.IsLB ∧ Presents ((m : ℕ) • divOf (fl.C k) (expo S.Dw w)) (L.pull M.j) r ∧ ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (fl.C k).Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι), spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) → ((m : ℕ) : ℝ) * lgOf (fl.C k) w v e y = Real.log (e.w (valAt y.1 (((eqn (divOf (fl.C k) (expo S.Dw w)) (below y.1))⁻¹ ^ (m : ℕ) * r i : (fl.C k).Y.Fnˣ) : (fl.C k).Y.Fn))) := by
  first | exact @GlobalTheory.LineNorm.exists_model_lgOf | exact GlobalTheory.LineNorm.exists_model_lgOf | (intros; apply GlobalTheory.LineNorm.exists_model_lgOf <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder

namespace GlobalTheory

open scoped ContDiff

theorem AnRead.smoothOn_conjTranspose_mul_mul :
    ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)), IsOpen S → ∀ (A M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.HoloOn S (fun y => A y a b)) → (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → ∀ a b : Fin m, R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).re) ∧ R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).im) := by
  intro k _ Y p σ D m R S hS A M hA hM a b
  have hC : ∀ i, ContDiffOn ℝ ∞ ((fun y => ((A y)ᴴ * M y * A y) a b) ∘ (R.chart i).e.symm)
      ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S) := by
    intro i
    set e := (R.chart i).e
    have hU := GlobalTheory.ChartGlue.isOpen_over e hS
    have hAe : ∀ c d, ContDiffOn ℝ ∞ (fun v => A (e.symm v) c d) (e.target ∩ e.symm ⁻¹' S) :=
      fun c d => GlobalTheory.ChartGlue.contDiffOn_real hU (hA c d i)
    have hAc : ∀ c d, ContDiffOn ℝ ∞ (fun v => star (A (e.symm v) c d)) (e.target ∩ e.symm ⁻¹' S) :=
      fun c d => Complex.conjCLE.contDiff.comp_contDiffOn (hAe c d)
    have hMe : ∀ c d, ContDiffOn ℝ ∞ (fun v => M (e.symm v) c d) (e.target ∩ e.symm ⁻¹' S) := by
      intro c d
      have h1 : ContDiffOn ℝ ∞ (fun v => (M (e.symm v) c d).re) (e.target ∩ e.symm ⁻¹' S) := (hM c d).1 i
      have h2 : ContDiffOn ℝ ∞ (fun v => (M (e.symm v) c d).im) (e.target ∩ e.symm ⁻¹' S) := (hM c d).2 i
      have hf : (fun v => M (e.symm v) c d) = fun v => (((M (e.symm v) c d).re : ℝ) : ℂ) +
          (((M (e.symm v) c d).im : ℝ) : ℂ) * Complex.I := by
        funext v; exact (Complex.re_add_im _).symm
      rw [hf]
      exact (Complex.ofRealCLM.contDiff.comp_contDiffOn h1).add
        ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2).mul contDiffOn_const)
    show ContDiffOn ℝ ∞ (fun v => ((A (e.symm v))ᴴ * M (e.symm v) * A (e.symm v)) a b) _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiffOn.sum fun x _ => (ContDiffOn.sum fun c _ => (hAc c a).mul (hMe c x)).mul (hAe x b)
  exact ⟨fun i => Complex.reCLM.contDiff.comp_contDiffOn (hC i),
    fun i => Complex.imCLM.contDiff.comp_contDiffOn (hC i)⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_hermitian_smooth : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)), IsOpen S → ∀ (A M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.HoloOn S (fun y => A y a b)) → (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → ∀ a b : Fin m, R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).re) ∧ R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).im) := by
  first | exact @GlobalTheory.AnRead.smoothOn_conjTranspose_mul_mul | exact GlobalTheory.AnRead.smoothOn_conjTranspose_mul_mul | (intros; apply GlobalTheory.AnRead.smoothOn_conjTranspose_mul_mul <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder

set_option autoImplicit false

open scoped ContDiff

namespace GlobalTheory

theorem smoothOn_log_grSq : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)) (M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → (∀ y ∈ S, (M y).PosDef) → ∀ i : Fin m, R.SmoothOn S (fun y => Real.log (grSq (M y) i)) := by
  intro k _ Y p σ D m R S M hM hP i j
  have hE : ∀ a b, ContDiffOn ℝ ∞ (fun v => M ((R.chart j).e.symm v) a b)
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' S) := fun a b => by
    have h1 := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hM a b).1 j)
    have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hM a b).2 j)
    refine (h1.add (h2.mul (contDiffOn_const (c := Complex.I)))).congr fun v _ => ?_
    simp [Function.comp_def, Complex.re_add_im]
  have hL : ∀ K : Fin (m + 1), ContDiffOn ℝ ∞ (fun v => ReciprocityTheory.ChartRestriction.G.FD.lminor (M ((R.chart j).e.symm v)) K)
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' S) := fun K => by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.lminor, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    exact ContDiffOn.sum fun π _ => contDiffOn_const.mul (contDiffOn_prod fun c _ => hE _ _)
  have hq := (hL i.succ).mul ((hL i.castSucc).inv fun v (hv : v ∈ (R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' S) =>
    (GlobalTheory.GradedNorm.lminor_pos (hP _ hv.2) _).ne')
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hq
  exact (hr.log fun v hv => (grSq_pos (hP _ hv.2) i).ne').congr fun v _ => by simp [grSq, div_eq_mul_inv]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_gram_square_smooth : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)) (M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → (∀ y ∈ S, (M y).PosDef) → ∀ i : Fin m, R.SmoothOn S (fun y => Real.log (grSq (M y) i)) := by
  atlas_forward_decl GlobalTheory.smoothOn_log_grSq
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.FlagFrames

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_frames_nhds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (y : Y.Y.X), ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Fr : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y.Y.X, U)), y ∈ U ∧ LogKS.chart V ≫ genStr Z = spMap φ ∧ (∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) ∧ (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧ ∀ (p : Y.Y.pts σ) (hp : p ∈ ptsIn Y.Y.str σ U), ∃ (hv : Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) (g f : Y.FrameAt p), Y.Adapted p t g 1 ∧ Fr.IsMap (evHom hv) f ∧ ∀ τ, f.co g τ = (A τ).map (evHom hp) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y σ y
  obtain ⟨V₀, hV₀, φ₀, Fr₀, hy₀, hs₀, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (Y.π y)
  obtain ⟨U, hU, hy, φ, fr, t, hle, hs, hT, ht⟩ := Spread.exists_frame_nhds E H Dw l Xo c O β Z F e Y y (Y.π ⁻¹ᵁ V₀) hy₀
  let ρ : Γ(gen Z, V₀) →+* Γ(Y.Y.X, U) := (Y.π.appLE V₀ U hle).hom
  have hρ : spMap ρ ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) =
      (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π := IsAffineOpen.SpecMap_appLE_fromSpec Y.π hV₀ hU hle

  have hφ : φ = ρ.comp φ₀ := EigLoc.spMap_inj (by
    rw [← hs, ← hρ, Category.assoc, hs₀]
    exact spMap_comp_spMap φ₀ ρ)
  have hxρ : ((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z =
      spMap ρ ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨Fr', hFr'⟩ := Fr₀.exists_isMap ρ hφ hxρ
  have hdown : ∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V₀ := fun p hp =>
    CxPts.mem_ptsIn.2 (hle (CxPts.mem_ptsIn.1 hp))
  refine ⟨U, t, ⟨V₀, hV₀⟩, φ₀, Fr₀, fun τ => Fr'.co fr τ, hy, hs₀, hdown, ht, fun p hp => ⟨hdown p hp, ?_⟩⟩
  have hv := hdown p hp
  have hpU : spMap (evHom hp) ≫ (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) = p.1 :=
    Points.specMap_valMap_fromSpec hU p.1 hp
  have hpV : spMap (evHom hv) ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) = (Y.down p).1 :=
    Points.specMap_valMap_fromSpec hV₀ (Y.down p).1 hv
  have hov : (Y.down p).1 ≫ genStr Z = spMap (embOf e σ) := (Y.down p).2
  have hxg : (Y.down p).1 ≫ genι Z = spMap (evHom hp) ≫ ((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z := by
    rw [← Category.assoc, ← Category.assoc, hpU]; rfl
  have hxf : (Y.down p).1 ≫ genι Z = spMap (evHom hv) ≫ (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec) ≫ genι Z := by
    rw [← Category.assoc, hpV]
  have hφg : embOf e σ = (evHom hp).comp φ := EigLoc.spMap_inj (hov.symm.trans (by
    rw [← spMap_comp_spMap φ (evHom hp), ← hs, ← Category.assoc, ← Category.assoc, hpU]; rfl))
  have hφf : embOf e σ = (evHom hv).comp φ₀ := EigLoc.spMap_inj (hov.symm.trans (by
    rw [← spMap_comp_spMap φ₀ (evHom hv), ← hs₀, ← Category.assoc, hpV]))
  have hev : (evHom hp).comp ρ = evHom hv := EigLoc.spMap_inj ((cancel_mono
    (show Sp Γ(gen Z, V₀) ⟶ gen Z from hV₀.fromSpec)).1 (by
      rw [hpV, ← spMap_comp_spMap ρ (evHom hp), Category.assoc, hρ, ← Category.assoc, hpU]; rfl))
  obtain ⟨g, hg⟩ := fr.exists_isMap (evHom hp) hφg hxg
  obtain ⟨f, hf⟩ := Fr₀.exists_isMap (evHom hv) hφf hxf
  have hf' : Fr'.IsMap (evHom hp) f := fun τ i => by
    rw [hf τ i, hFr' τ i, GradedPieces.dual_comp, hev]
  refine ⟨g, f, ?_, hf, fun τ => EigFrame.IsMap.co τ hf' hg hxg⟩
  have hb : Var.base p ∈ U := CxPts.mem_ptsIn.1 hp
  let gm : Γ(Y.Y.X, U) →+* Y.Y.X.presheaf.stalk (Var.base p) := (Y.Y.X.presheaf.germ U (Var.base p) hb).hom
  have hxs : stalkPt Y.Y (Var.base p) ≫ Y.π ≫ genι Z =
      spMap gm ≫ ((show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) ≫ Y.π) ≫ genι Z := by
    have h0 : stalkPt Y.Y (Var.base p) = spMap gm ≫ (show Sp Γ(Y.Y.X, U) ⟶ Y.Y.X from hU.fromSpec) :=
      (Spread.spMap_germ hU hb).symm
    rw [h0]; simp only [Category.assoc]
  obtain ⟨frs, hfrs⟩ := fr.exists_isMap gm rfl hxs
  have hgm : (Var.evStalk p).comp gm = evHom hp :=
    (congrArg CommRingCat.Hom.hom (HolFrames.valR_eq_germ p.1 U hp)).symm
  have hgs : frs.IsMap (Var.evStalk p) g := fun τ i => by
    rw [hg τ i, hfrs τ i, GradedPieces.dual_comp, hgm]
  have hxp : (Y.down p).1 ≫ genι Z = spMap (Var.evStalk p) ≫ stalkPt Y.Y (Var.base p) ≫ Y.π ≫ genι Z := by
    rw [← Category.assoc, Y.spMap_evStalk p]; rfl
  have hκ : (algebraMap (Y.Y.X.presheaf.stalk (Var.base p)) Y.Y.X.functionField).comp gm = fnOf U (gen_mem hy) :=
    RingHom.ext fun a => algebraMap_germ _ a
  have ha : frs.Tri (algebraMap _ Y.Y.X.functionField) Y.f0 t := by
    refine ⟨by rw [hT.1, hxs, ← hκ, ← spMap_comp_spMap gm, Category.assoc], by rw [hT.2.1, ← hκ]; rfl, fun τ i => ?_⟩
    have h3 := hT.2.2 τ i
    rw [← hκ] at h3
    simpa only [hfrs τ, GradedPieces.dual_comp] using h3
  have hφs : embOf e σ = (Var.evStalk p).comp (gm.comp φ) := by
    rw [hφg, ← hgm]; rfl
  exact (FlagCpt.adapted_of_tri (Y.spMap_evStalk p).symm ha (hgs.tri hφs hxp)).1

end GlobalTheory.ShFam.FlagFrames
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_flag_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (y : Y.Y.X), ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Fr : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y.Y.X, U)), y ∈ U ∧ LogKS.chart V ≫ genStr Z = spMap φ ∧ (∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) ∧ (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧ ∀ (p : Y.Y.pts σ) (hp : p ∈ ptsIn Y.Y.str σ U), ∃ (hv : Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) (g f : Y.FrameAt p), Y.Adapted p t g 1 ∧ Fr.IsMap (evHom hv) f ∧ ∀ τ, f.co g τ = (A τ).map (evHom hp) := by
  first | exact @GlobalTheory.ShFam.FlagFrames.exists_frames_nhds | exact GlobalTheory.ShFam.FlagFrames.exists_frames_nhds | (intros; apply GlobalTheory.ShFam.FlagFrames.exists_frames_nhds <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam.FlagCpt

theorem smoothOn_met_of_eigMet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (G : EigMet Z (embOf e σ)) (T : Set (CxPts (genStr Z) (embOf e σ))), IsOpen T → G.SmoothOn (manifold Z (embOf e σ)) T → ∀ n : Pad.Letter Dw → ℤ, IsOpen (Y.down ⁻¹' T : Set (Y.Y.pts σ)) ∧ (Y.met G n).SmoothOn (Y.down ⁻¹' T) := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ F _ _ e Y σ G T hT hG n
  have hc : Continuous (Y.down (σ := σ)) := CxPts.continuous_of_comp (f := Y.π) (fun _ => rfl)
  have hS : IsOpen (Y.down ⁻¹' T : Set (Y.Y.pts σ)) := hT.preimage hc
  refine ⟨hS, ?_⟩
  have key : ∀ y : Y.Y.X, ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ), y ∈ U ∧
      (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧
      (Y.Y.an σ).SmoothOn (Y.down ⁻¹' T ∩ ptsIn Y.Y.str σ U) (fun q => Real.log ((Y.met G n).h (prodPow t n) q)) := by
    intro y
    obtain ⟨U, t, V, φ, Fr, A, hy, hφ, hUV, ht, hfr⟩ := GlobalTheory.T.exists_local_flag_coordinates E H Dw l Xo c O β Z F e Y σ y
    refine ⟨U, t, hy, ht, ?_⟩
    choose gf hre him hgf using fun (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)) => hG V φ Fr τ a b hφ
    set S' : Set (Y.Y.pts σ) := Y.down ⁻¹' T ∩ ptsIn Y.Y.str σ U with hS'def
    have hS' : IsOpen S' := hS.inter (isOpen_ptsIn _)
    have hsub : S' ⊆ Y.down ⁻¹' (T ∩ ptsIn _ _ V.1) := fun q hq => ⟨hq.1, hUV q hq.2⟩
    let Mf : ∀ τ : E →+* ℂ, Y.Y.pts σ → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun τ q => Matrix.of fun a b => gf τ a b (Y.down q)
    let Af : ∀ τ : E →+* ℂ, Y.Y.pts σ → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
      fun τ q => Matrix.of fun a b => ev Y.Y.str σ U (A τ a b) q
    have hM : ∀ τ a b, (Y.Y.an σ).SmoothOn S' (fun q => (Mf τ q a b).re) ∧ (Y.Y.an σ).SmoothOn S' (fun q => (Mf τ q a b).im) :=
      fun τ a b => ⟨((hre τ a b).comp_map (hT.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl) (Y.Y.an σ)).mono hsub,
        ((him τ a b).comp_map (hT.inter (isOpen_ptsIn _)) (m := Y.down) (f := Y.π) (fun _ => rfl) (Y.Y.an σ)).mono hsub⟩
    have hA : ∀ τ a b, (Y.Y.an σ).HoloOn S' (fun q => Af τ q a b) :=
      fun τ a b => AnRead.holoOn_ev_of_subset _ (fun _ hq => hq.2)
    have hgram : ∀ q ∈ S', ∃ g : Y.FrameAt q, Y.Adapted q t g 1 ∧
        ∀ τ, G.gram (Y.down q) g τ = (Af τ q)ᴴ * Mf τ q * Af τ q := by
      intro q hq
      obtain ⟨hv, g, f, had, hmap, hco⟩ := hfr q hq.2
      refine ⟨g, had, fun τ => ?_⟩
      have e1 : f.co g τ = Af τ q := by
        rw [hco τ]; ext a b; simp [Af, ev_eq hq.2]
      have e2 : G.gram (Y.down q) f τ = Mf τ q := by
        ext a b; exact hgf τ a b (Y.down q) hq.1 hv f hmap
      rw [G.change _ f g τ, e1, e2]
    have hpos : ∀ τ, ∀ q ∈ S', ((Af τ q)ᴴ * Mf τ q * Af τ q).PosDef := fun τ q hq => by
      obtain ⟨g, -, hg⟩ := hgram q hq
      rw [← hg τ]; exact G.pos _ _ _
    have hsm : ∀ z : Letter Dw, (Y.Y.an σ).SmoothOn S' (fun q => Real.log (grSq ((Af z.1 q)ᴴ * Mf z.1 q * Af z.1 q) z.2)) :=
      fun z => GlobalTheory.T.log_gram_square_smooth _ S' _ (GlobalTheory.T.conjugate_hermitian_smooth _ S' hS' _ _ (hA z.1) (hM z.1)) (hpos z.1) z.2
    refine AnRead.SmoothOn.congr (f := fun q => ∑ z : Letter Dw, (n z : ℝ) * Real.log (grSq ((Af z.1 q)ᴴ * Mf z.1 q * Af z.1 q) z.2))
      (fun i => ContDiffOn.sum fun z _ => contDiffOn_const.mul (hsm z i)) fun q hq => ?_
    obtain ⟨g, had, hg⟩ := hgram q hq
    rw [FlagCpt.met_h G n had]
    simp only [prodPow, FlagCpt.genSq, hg, Pi.one_apply, _root_.one_zpow, Finset.prod_const_one, Units.val_one, norm_one, one_pow, div_one]
    rw [Real.log_prod (fun z _ => (zpow_pos (grSq_pos (hpos z.1 q hq) z.2) (n z)).ne')]
    exact Finset.sum_congr rfl fun z _ => Real.log_zpow _ _
  choose U t hy ht hs using key
  refine Var.Met.smoothOn_of_cover hS (fun q _ => by rw [FlagCpt.posSet_met]; exact Set.mem_univ q)
    (T := fun y => ptsIn Y.Y.str σ (U y)) (fun _ => isOpen_ptsIn _) (fun q => ⟨Var.base q, mem_ptsIn.2 (hy _)⟩)
    (e := fun y => prodPow (t y) n) (fun y q hq => FlagCpt.prodPow_mem n (fun τ i => ht y _ (mem_ptsIn.1 hq) τ i))
    fun y => ?_
  refine AnRead.SmoothOn.congr (f := fun q => -Real.log ((Y.met G n).h (prodPow (t y) n) q)) (fun i => (hs y i).neg) ?_
  exact fun q _ => rfl

end GlobalTheory.ShFam.FlagCpt
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_metric_flag_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (G : EigMet Z (embOf e σ)) (T : Set (CxPts (genStr Z) (embOf e σ))), IsOpen T → G.SmoothOn (manifold Z (embOf e σ)) T → ∀ n : Pad.Letter Dw → ℤ, IsOpen (Y.down ⁻¹' T : Set (Y.Y.pts σ)) ∧ (Y.met G n).SmoothOn (Y.down ⁻¹' T) := by
  first | exact @GlobalTheory.ShFam.FlagCpt.smoothOn_met_of_eigMet | exact GlobalTheory.ShFam.FlagCpt.smoothOn_met_of_eigMet | (intros; apply GlobalTheory.ShFam.FlagCpt.smoothOn_met_of_eigMet <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ShFam.InterpSmooth

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {U : Set E'}

theorem contDiffOn_iff_re_im {f : E' → ℂ} : ContDiffOn ℝ ∞ f U ↔
    ContDiffOn ℝ ∞ (fun v => (f v).re) U ∧ ContDiffOn ℝ ∞ (fun v => (f v).im) U := by
  refine ⟨fun h => ⟨Complex.reCLM.contDiff.comp_contDiffOn h, Complex.imCLM.contDiff.comp_contDiffOn h⟩, fun h => ?_⟩
  have := (Complex.ofRealCLM.contDiff.comp_contDiffOn h.1).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn h.2).mul (contDiffOn_const (c := Complex.I)))
  refine this.congr fun v _ => ?_
  simp [Complex.re_add_im]

variable {n : ℕ}

def EntSm (A : E' → Matrix (Fin n) (Fin n) ℂ) (U : Set E') : Prop := ∀ a b, ContDiffOn ℝ ∞ (fun v => A v a b) U

theorem det_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (h : EntSm A U) : ContDiffOn ℝ ∞ (fun v => (A v).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem inv_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (h : EntSm A U) (h0 : ∀ v ∈ U, (A v).det ≠ 0) :
    EntSm (fun v => (A v)⁻¹) U := by
  intro a b
  have hadj : ContDiffOn ℝ ∞ (fun v => (A v).adjugate a b) U := by
    simp only [Matrix.adjugate_apply]
    refine det_sm (A := fun v => (A v).updateRow b (Pi.single a 1)) fun i k => ?_
    by_cases hi : i = b
    · simp only [Matrix.updateRow_apply, hi, ↓reduceIte]
      exact contDiffOn_const
    · simp only [Matrix.updateRow_apply, hi, ↓reduceIte]
      exact h _ _
  refine (((det_sm h).inv h0).mul hadj).congr fun v _ => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Pi.inv_apply]

theorem mix_sm {s : E' → ℝ} {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hs : ContDiffOn ℝ ∞ s U) (hA : EntSm A U)
    (hB : EntSm B U) : EntSm (fun v => mix (s v) (A v) (B v)) U := fun a b => by
  have hs' : ContDiffOn ℝ ∞ (fun v => ((s v : ℝ) : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hs
  have h1 : ContDiffOn ℝ ∞ (fun v => ((1 - s v : ℝ) : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.sub hs)
  refine ((h1.mul (hA a b)).add (hs'.mul (hB a b))).congr fun v _ => ?_
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem dual_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (hA : EntSm A U) (hp : ∀ v ∈ U, (A v).PosDef) :
    EntSm (fun v => dualGram (A v)) U :=
  fun a b => (inv_sm hA (fun v hv => (hp v hv).det_pos.ne') b a).congr fun _ _ => rfl

theorem mixDual_sm {s : E' → ℝ} {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hs : ContDiffOn ℝ ∞ s U) (hA : EntSm A U)
    (hB : EntSm B U) (hpA : ∀ v ∈ U, (A v).PosDef) (hpB : ∀ v ∈ U, (B v).PosDef)
    (hs01 : ∀ v ∈ U, s v ∈ Set.Icc (0 : ℝ) 1) : EntSm (fun v => mixDual (s v) (A v) (B v)) U :=
  dual_sm (mix_sm hs (dual_sm hA hpA) (dual_sm hB hpB)) fun v hv =>
    mix_posDef (hs01 v hv) (dualGram_posDef (hpA v hv)) (dualGram_posDef (hpB v hv))

theorem ite_sm {c : Prop} [Decidable c] {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hA : EntSm A U) (hB : EntSm B U) :
    EntSm (fun v => if c then A v else B v) U := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact hA
  · simp only [hc, ↓reduceIte]; exact hB

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end GlobalTheory.ShFam.InterpSmooth

namespace GlobalTheory.ShFam

open InterpSmooth

theorem ToroidalCompactificationData.smoothOn_eigMetAt_some : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ)
    (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (R : ℝ), 2 ≤ R →
    (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} →
    (x.eigMetAt σ (some R)).SmoothOn (manifold s.T.Z σ) Set.univ := by
  intro D A N j S κ s x σ R hR hH V φ F τ a b hφ
  classical
  set P := ptsIn (genStr s.T.Z) σ V.1 with hP
  set Bc := {y : CxPts (genStr s.T.Z) σ | ¬ LiesIn y (genBd s.T.Z)} with hBc
  have hBo : IsOpen Bc := isOpen_not_liesIn _

  have hphi : ∀ y (hy : y ∈ P), σ = (evHom hy).comp φ := fun y hy => by
    have e : spMap σ = spMap ((evHom hy).comp φ) := by
      rw [← y.2, ← spMap_evHom hy, Category.assoc, hφ, ← Spec.map_comp]; rfl
    exact spMap_inj e
  have hfr : ∀ y (hy : y ∈ P), ∃ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), F.IsMap (evHom hy) f := fun y hy =>
    F.exists_isMap (evHom hy) (hphi y hy) (by rw [← Category.assoc, spMap_evHom hy])
  have huniq : ∀ y (hy : y ∈ P) (f f' : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f →
      F.IsMap (evHom hy) f' → f = f' := fun y hy f f' hf hf' => by
    have e : f.v = f'.v := funext fun τ => funext fun i => (hf τ i).trans (hf' τ i).symm
    cases f; cases f'
    cases e
    rfl

  choose g0 hg0r hg0i hg0 using fun a' b' => x.smoothOn_eigMet σ V φ F τ a' b' hφ
  choose g1 hg1r hg1i hg1 using fun a' b' => hH V φ F τ a' b' hφ
  let M0 := fun y => Matrix.of fun a' b' => g0 a' b' y
  let M1 := fun y => Matrix.of fun a' b' => g1 a' b' y
  have e0 : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMet σ).gram y f τ = M0 y := fun y hy f hf =>
    Matrix.ext fun a' b' => hg0 a' b' y (Set.mem_univ y) hy f hf
  have e1 : ∀ y (hy : y ∈ P), y ∈ Bc → ∀ f, F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ = M1 y :=
    fun y hy hb f hf => Matrix.ext fun a' b' => hg1 a' b' y hb hy f hf
  have p0 : ∀ y ∈ P, (M0 y).PosDef := fun y hy => by
    obtain ⟨f, hf⟩ := hfr y hy
    exact e0 y hy f hf ▸ (x.eigMet σ).pos y f τ
  have p1 : ∀ y ∈ P, y ∈ Bc → (M1 y).PosDef := fun y hy hb => by
    obtain ⟨f, hf⟩ := hfr y hy
    exact e1 y hy hb f hf ▸ (x.hodge σ).pos y f τ

  let g : CxPts (genStr s.T.Z) σ → ℂ := fun y =>
    if hy : y ∈ P then (x.eigMetAt σ (some R)).gram y (hfr y hy).choose τ a b else 0
  have hg : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMetAt σ (some R)).gram y f τ a b = g y :=
    fun y hy f hf => by
      simp only [g, dif_pos hy]
      rw [huniq y hy f _ hf (hfr y hy).choose_spec]

  set W := {y : CxPts (genStr s.T.Z) σ | (∏ i, x.nrm σ i y) ^ 2 < Real.exp (Real.exp 1 - R ^ 3)} with hW
  have hcont : ∀ i, Continuous (x.nrm σ i) := fun i => continuous_iff_continuousAt.2 fun y => by
    obtain ⟨V', t, f, hy, -, hf, e⟩ := (x.nrm_div σ i).2 y
    have ho := isOpen_ptsIn (p := genStr s.T.Z) (σ := σ) V'.1
    have h1 : ContinuousOn (fun z => √(‖ev (genStr s.T.Z) σ V'.1 t z‖ ^ 2 * Real.exp (-f z))) (ptsIn _ σ V'.1) :=
      (((((manifold s.T.Z σ).holoOn_ev V'.1 t).continuousOn ho).norm.pow 2).mul
        ((hf.continuousOn ho).neg.rexp)).sqrt
    refine (h1.continuousAt (ho.mem_nhds hy)).congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hy) fun z hz => ?_)
    rw [← e z hz, Real.sqrt_sq ((x.nrm_div σ i).1 z).1]
  have hWo : IsOpen W := isOpen_lt ((continuous_finset_prod _ fun i _ => hcont i).pow 2) continuous_const
  have hWbd : ∀ y, LiesIn y (genBd s.T.Z) → y ∈ W := fun y hy => by
    obtain ⟨i, hi⟩ := (x.liesIn_genBd_iff y).1 hy
    have h0 : x.nrm σ i y = 0 :=
      le_antisymm (not_lt.1 fun h => ((x.nrm_div σ i).pos_iff y).1 h hi) ((x.nrm_div σ i).1 y).1
    show (∏ i, x.nrm σ i y) ^ 2 < _
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    simpa using Real.exp_pos _
  have hW0 : ∀ y ∈ W, x.wt σ R y = 0 := fun y hy => by
    by_cases hL : LiesIn y (genBd s.T.Z)
    · exact x.wt_eq_zero hR (Or.inl hL)
    · refine x.wt_eq_zero hR (Or.inr ?_)
      have hpos : 0 < (∏ i, x.nrm σ i y) ^ 2 := pow_pos (Finset.prod_pos fun i _ => x.nrm_pos hL i) 2
      have := (Real.log_lt_iff_lt_exp hpos).2 hy
      simp only [OddPrimesWithRootsOfUnity.r]
      linarith

  have hr : (manifold s.T.Z σ).SmoothOn Bc (x.r σ) := by
    refine AnRead.SmoothOn.congr (f := fun y => Real.exp 1 - ∑ i, Real.log (x.nrm σ i y ^ 2))
      (fun c => contDiffOn_const.sub (ContDiffOn.sum fun i _ => ((x.nrm_div σ i).smoothOn_log.mono
        fun y (hy : ¬ LiesIn y (genBd s.T.Z)) hi => hy ((x.liesIn_genBd_iff y).2 ⟨i, hi⟩)) c)) fun y hy => ?_
    simp only [OddPrimesWithRootsOfUnity.r]
    rw [← Finset.prod_pow, Real.log_prod fun i _ => pow_ne_zero _ (x.nrm_pos hy i).ne']
  have hw : (manifold s.T.Z σ).SmoothOn Bc (x.wt σ R) := by
    refine AnRead.SmoothOn.congr (f := fun y => cutWt x.kap R (x.r σ y)) (fun c => ?_) fun y hy => x.wt_eq hR hy
    have h1 := hr c
    have hpos : ∀ v, 0 < (x.r σ ∘ ((manifold s.T.Z σ).chart c).e.symm) v := fun v =>
      lt_of_lt_of_le (Real.exp_pos 1) (x.exp_le_r σ _)
    have hA := contDiff_cutoff.1.comp_contDiffOn ((h1.log fun v _ => (hpos v).ne').div_const (Real.log R))
    have hB := contDiffOn_const (c := (1 : ℝ)).add ((h1.div_const R).rpow_const_of_ne (p := x.kap)
      fun v _ => (div_pos (hpos v) (by linarith)).ne')
    refine (hA.div hB fun v _ => ?_).congr fun v _ => rfl
    exact (add_pos_of_pos_of_nonneg one_pos (Real.rpow_nonneg (div_nonneg (hpos v).le (by linarith)) _)).ne'

  have hgB : ∀ y ∈ P, y ∈ Bc → g y = (if τ (A.H.rt : D.host.E) = A.H.rt0 then mix (x.wt σ R y) (M0 y) (M1 y)
      else mixDual (x.wt σ R y) (M0 y) (M1 y)) a b := fun y hy hb => by
    obtain ⟨f, hf⟩ := hfr y hy
    rw [← hg y hy f hf]
    simp only [ToroidalCompactificationData.eigMetAt, EigMet.interp]
    rw [e0 y hy f hf, e1 y hy hb f hf]

  have hgW : ∀ y ∈ P, y ∈ W → g y = g0 a b y := fun y hy hw' => by
    obtain ⟨f, hf⟩ := hfr y hy
    rw [← hg y hy f hf, ← hg0 a b y (Set.mem_univ y) hy f hf]
    exact congrFun (congrFun (EigMet.interp_gram_zero (hs := x.wt_mem R) f (hW0 y hw')) a) b

  let T : Bool → Set (CxPts (genStr s.T.Z) σ) := fun β => cond β W Bc
  have key : ∀ β i, ContDiffOn ℝ ∞ (g ∘ ((manifold s.T.Z σ).chart i).e.symm)
      (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β)) := by
    intro β i
    have sub : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β) ⊆
        ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Set.univ ∩ P) :=
      fun v hv => ⟨hv.1, hv.2.1⟩
    have s0 : EntSm (fun v => M0 (((manifold s.T.Z σ).chart i).e.symm v))
        (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β)) :=
      fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg0r a' b' i).mono sub, (hg0i a' b' i).mono sub⟩
    cases β
    · have sub1 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹'
          ((Set.univ ∩ P) ∩ T false) ⊆
          ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Bc ∩ P) :=
        fun v hv => ⟨hv.1, hv.2.2, hv.2.1.2⟩
      have sub2 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹'
          ((Set.univ ∩ P) ∩ T false) ⊆
          ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' Bc :=
        fun v hv => ⟨hv.1, hv.2.2⟩
      have s1 : EntSm (fun v => M1 (((manifold s.T.Z σ).chart i).e.symm v)) _ :=
        fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg1r a' b' i).mono sub1, (hg1i a' b' i).mono sub1⟩
      have sw := (hw i).mono sub2
      have hf := ite_sm (c := τ (A.H.rt : D.host.E) = A.H.rt0) (mix_sm sw s0 s1)
        (mixDual_sm sw s0 s1 (fun v hv => p0 _ hv.2.1.2) (fun v hv => p1 _ hv.2.1.2 hv.2.2)
          fun v _ => x.wt_mem R _) a b
      refine hf.congr fun v hv => ?_
      simp only [Function.comp]
      rw [hgB _ hv.2.1.2 hv.2.2]
    · refine (s0 a b).congr fun v hv => ?_
      simp only [Function.comp]
      exact hgW _ hv.2.1.2 hv.2.2
  have hT : ∀ β, IsOpen (T β) := fun β => by cases β; exacts [hBo, hWo]
  have hc : ∀ y ∈ Set.univ ∩ P, ∃ β, y ∈ T β := fun y _ => by
    by_cases hL : LiesIn y (genBd s.T.Z)
    · exact ⟨true, hWbd y hL⟩
    · exact ⟨false, hL⟩
  refine ⟨g, AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).1,
    AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).2, fun y _ hy f hf => hg y hy f hf⟩

end GlobalTheory.ShFam
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_metric_smooth_of_hodge : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (R : ℝ), 2 ≤ R → (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} → (x.eigMetAt σ (some R)).SmoothOn (manifold s.T.Z σ) Set.univ := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.smoothOn_eigMetAt_some | exact GlobalTheory.ShFam.ToroidalCompactificationData.smoothOn_eigMetAt_some | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.smoothOn_eigMetAt_some <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory

theorem metsOf_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ), (∀ R : ℝ, 2 ≤ R → (cxSt D.what₂.LL).mSmooth _ σ _ (metsOf x Φ k (some R) σ n)) ∧ (cxSt D.what₂.LL).mSmooth _ σ _ (refMet x Φ k σ n) ∧ Var.Met.SmoothOn (metsOf x Φ k none σ n) {p | (Φ.C k).π (Var.base p) ∉ genBd s.T.Z} := by
  intro D A N j S κ s x Φ k σ n
  exact ⟨fun R hR => (GlobalTheory.T.eigen_metric_flag_compactification _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ _ _ isOpen_univ
      (GlobalTheory.T.eigen_metric_smooth_of_hodge D A N j S κ s x _ R hR (GlobalTheory.T.hodge_metric_smooth_off_boundary D A N j S κ s x _)) n).2,
    (GlobalTheory.T.eigen_metric_flag_compactification _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ _ _ isOpen_univ (x.smoothOn_eigMet _) n).2,
    (GlobalTheory.T.eigen_metric_flag_compactification _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ _ _ (isOpen_not_liesIn _) (GlobalTheory.T.hodge_metric_smooth_off_boundary D A N j S κ s x _) n).2⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_metrics_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ), (∀ R : ℝ, 2 ≤ R → (cxSt D.what₂.LL).mSmooth _ σ _ (metsOf x Φ k (some R) σ n)) ∧ (cxSt D.what₂.LL).mSmooth _ σ _ (refMet x Φ k σ n) ∧ Var.Met.SmoothOn (metsOf x Φ k none σ n) {p | (Φ.C k).π (Var.base p) ∉ genBd s.T.Z} := by
  first | exact @GlobalTheory.metsOf_smooth | exact GlobalTheory.metsOf_smooth | (intros; apply GlobalTheory.metsOf_smooth <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.ConjMet

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.ShFam.FlagCpt
open scoped ComplexOrder

theorem map_conj_eq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : M.map (starRingEnd ℂ) = Mᴴᵀ := by
  ext a b; simp

theorem mix_map_conj {m : ℕ} (s : ℝ) (M₀ M : Matrix (Fin m) (Fin m) ℂ) :
    mix s (M₀.map (starRingEnd ℂ)) (M.map (starRingEnd ℂ)) = (mix s M₀ M).map (starRingEnd ℂ) := by
  ext a b; simp [mix]

theorem dualGram_map_conj {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    dualGram (M.map (starRingEnd ℂ)) = (dualGram M).map (starRingEnd ℂ) := by
  rw [dualGram, dualGram, map_conj_eq, map_conj_eq, ← transpose_nonsing_inv (Mᴴ), ← conjTranspose_nonsing_inv]
  ext a b; simp

theorem mixDual_map_conj {m : ℕ} (s : ℝ) (M₀ M : Matrix (Fin m) (Fin m) ℂ) :
    mixDual s (M₀.map (starRingEnd ℂ)) (M.map (starRingEnd ℂ)) = (mixDual s M₀ M).map (starRingEnd ℂ) := by
  rw [mixDual, mixDual, dualGram_map_conj, dualGram_map_conj, mix_map_conj, dualGram_map_conj]

theorem smul_gram_map_conj {m : ℕ} (b : ℝ) (T : Matrix (Fin m) (Fin m) ℂ) :
    (b : ℂ) • ((T.map (starRingEnd ℂ))ᴴ * T.map (starRingEnd ℂ)) = ((b : ℂ) • (Tᴴ * T)).map (starRingEnd ℂ) := by
  ext a c; simp [Matrix.mul_apply, map_sum]

theorem spMap_conj_conj : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext Complex.conj_conj))

theorem conj_comp_conj {A : Type} [CommRing A] (σ : A →+* ℂ) :
    (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ :=
  RingHom.ext fun a => Complex.conj_conj (σ a)

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_conj_symm {σ σ' : c.F →+* ℂ} {x x' : Sp ℂ ⟶ Z.X} {f : EigFrame Z σ x} {f' : EigFrame Z σ' x'}
    (h : f.IsMap (starRingEnd ℂ) f') : f'.IsMap (starRingEnd ℂ) f := fun τ i => by
  rw [h, GlobalTheory.GradedPieces.dual_comp, show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from
    RingHom.ext Complex.conj_conj, spMap_dualMap_id, Category.id_comp]

variable {σ σ' : c.F →+* ℂ} {y : CxPts (genStr Z) σ} {y' : CxPts (genStr Z) σ'}

theorem gen_eq (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    y'.1 ≫ genι Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι Z := by
  rw [e, Category.assoc]

theorem gen_eq' (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    y.1 ≫ genι Z = spMap (starRingEnd ℂ) ≫ y'.1 ≫ genι Z := by
  rw [e, ← Category.assoc, ← Category.assoc, spMap_conj_conj, Category.id_comp]

theorem r_conj [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (hσ : σ' = (starRingEnd ℂ).comp σ)
    (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) : x.r σ' y' = x.r σ y := by
  subst hσ
  let j : CxPts (genStr Z) σ → CxPts (genStr Z) ((starRingEnd ℂ).comp σ) :=
    fun z => ⟨spMap (starRingEnd ℂ) ≫ z.1, by rw [Category.assoc, z.2, ← Spec.map_comp]; rfl⟩
  have hj : IsConjMap j := fun _ => rfl
  have hy : j y = y' := Subtype.ext e.symm
  simp only [OddPrimesWithRootsOfUnity.r, fun i => x.nrm_conj _ _ j hj i y, hy]

end Free

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem tri_conj {R : Type} [CommRing R] {φ : c.F →+* R} {x0 : Sp R ⟶ Z.X} {f : EigFrame Z φ x0} {ψ : R →+* ℂ}
    {σ₁ σ₂ : c.F →+* ℂ} {x1 x2 : Sp ℂ ⟶ Z.X} {g : EigFrame Z σ₁ x1} {g' : EigFrame Z σ₂ x2}
    (h : f.Tri ψ g 1) (hg : g.IsMap (starRingEnd ℂ) g') (hσ : σ₂ = (starRingEnd ℂ).comp σ₁)
    (hx : x2 = spMap (starRingEnd ℂ) ≫ x1) : f.Tri ((starRingEnd ℂ).comp ψ) g' 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hx, h1, ← Category.assoc, spMap_comp_spMap], by rw [hσ, h2]; rfl, fun τ i => ?_⟩
  obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
  refine ⟨fun k => starRingEnd ℂ (cf k), by simp [c1], fun k hk => by simp [c2 k hk], ?_⟩
  have := GlobalTheory.GradedPieces.comb_map (starRingEnd ℂ) hx.symm c3
  simpa only [GlobalTheory.GradedPieces.dual_comp, ← hg τ i] using this

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : FlagCpt Z e} {σ σ' : F →+* ℂ} {p : Y.Y.pts σ} {p' : Y.Y.pts σ'}

theorem emb_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) : σ' = (starRingEnd ℂ).comp σ := by
  have h : spMap ((starRingEnd ℂ).comp σ) = spMap σ' := by
    rw [← p'.2, e', Category.assoc, p.2, ← Spec.map_comp]; rfl
  exact (EigLoc.spMap_inj h).symm

theorem embOf_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    embOf e σ' = (starRingEnd ℂ).comp (embOf e σ) := by
  rw [emb_conj e']; rfl

theorem base_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) : Var.base p' = Var.base p := by
  show p'.1 _ = p.1 _
  rw [e']
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))

theorem down_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) :
    (Y.down p').1 = spMap (starRingEnd ℂ) ≫ (Y.down p).1 := by
  show p'.1 ≫ Y.π = _
  rw [e', Category.assoc]; rfl

theorem met_h_conj (e' : p'.1 = spMap (starRingEnd ℂ) ≫ p.1) {G : EigMet Z (embOf e σ)} {G' : EigMet Z (embOf e σ')}
    (hG : ∀ (g : Y.FrameAt p) (g' : Y.FrameAt p') τ, g.IsMap (starRingEnd ℂ) g' →
      G'.gram (Y.down p') g' τ = (G.gram (Y.down p) g τ).map (starRingEnd ℂ))
    (n : Letter Dw → ℤ) {a : Y.Y.Fnˣ} (ha : p ∈ Var.eqnSet σ (divOf Y n) a) :
    (Y.met G' n).h a p' = (Y.met G n).h a p := by
  have hb : Var.base p' = Var.base p := base_conj e'
  obtain ⟨q, h1, h2⟩ := Y.exists_adapted p
  obtain ⟨φ, f, ta, tb⟩ := h2
  obtain ⟨g', hg'⟩ := q.2.exists_isMap (starRingEnd ℂ) (embOf_conj e') (gen_eq (down_conj e'))
  have hp : p'.1 = spMap ((starRingEnd ℂ).comp (Var.evStalk p)) ≫ stalkPt Y.Y (Var.base p) := by
    rw [e', ← Y.spMap_evStalk p, ← Category.assoc, spMap_comp_spMap]
  obtain ⟨ad', hv⟩ := adapted_of_tri hp ta (tri_conj tb hg' (embOf_conj e') (gen_eq (down_conj e')))
  have ha' : p' ∈ Var.eqnSet σ' (divOf Y n) a := by
    show (divOf Y n).IsEqn (Var.base p') a
    rw [hb]; exact ha
  have hP := prodPow_mem n h1
  have hP' := prodPow_mem n ad'.mem_eqnSet
  rw [(Y.met G' n).trans a _ p' ha' hP', (Y.met G n).trans a _ p ha hP, met_h G' n ad', met_h G n ⟨φ, f, ta, tb⟩]
  have hgen : Y.genSq G' n g' = Y.genSq G n q.2 := by
    unfold FlagCpt.genSq
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [hG q.2 g' z.1 hg', grSq_map_conj]
  have h0 := Var.tv_ne_zero ha hP
  rw [Var.tv] at h0
  obtain ⟨r, -, hr⟩ := Var.val_cx_ne_zero_iff.1 h0
  have htv : ‖Var.tv a (prodPow q.1 n) p'‖ = ‖Var.tv a (prodPow q.1 n) p‖ := by
    rw [Var.tv, Var.tv, ← hr, hv, (Var.hasVal_cx_stalk (y := p) r).val_eq, RingHom.comp_apply, Complex.norm_conj]
  rw [htv, hgen]

end Flag

section Tor

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
  {σ σ' : κ.c.F →+* ℂ} {y : CxPts (genStr s.T.Z) σ} {y' : CxPts (genStr s.T.Z) σ'}
  {g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)} {g' : EigFrame s.T.Z σ' (y'.1 ≫ genι s.T.Z)}

theorem eigMet_conj (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hg : g.IsMap (starRingEnd ℂ) g')
    (τ : D.host.E →+* ℂ) : (x.eigMet σ').gram y' g' τ = ((x.eigMet σ).gram y g τ).map (starRingEnd ℂ) :=
  OddPrimesWithRootsOfUnity.gram_conj x e g g' τ (hg τ)

theorem hodge_conj (hσ : σ' = (starRingEnd ℂ).comp σ) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    (hg : g.IsMap (starRingEnd ℂ) g') (τ : D.host.E →+* ℂ) :
    (x.hodge σ').gram y' g' τ = ((x.hodge σ).gram y g τ).map (starRingEnd ℂ) := by
  by_cases hb : LiesIn y (genBd s.T.Z)
  · rw [x.hodge_gram_of_liesIn ((liesIn_iff_of_comp e _).2 hb), x.hodge_gram_of_liesIn hb]
    exact OddPrimesWithRootsOfUnity.gram_conj x e g g' τ (hg τ)
  · obtain ⟨f', hf'⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 (fun h => hb ((liesIn_iff_of_comp e _).1 h))
    obtain ⟨f, hfm⟩ := f'.exists_isMap (starRingEnd ℂ) (φ' := σ) (x' := y.1 ≫ genι s.T.Z)
      (by rw [hσ, conj_comp_conj]) (gen_eq' e)
    have hf : IsHodgeFrame s.U y f := hf'.conj hσ e (isMap_conj_symm hfm)
    rw [x.hodge_gram hf' g' τ, x.hodge_gram hf g τ, (isMap_conj_symm hfm).co τ hg (gen_eq e)]
    exact smul_gram_map_conj _ _

theorem wt_conj (hσ : σ' = (starRingEnd ℂ).comp σ) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (R : ℝ) :
    x.wt σ' R y' = x.wt σ R y := by
  rw [ToroidalCompactificationData.wt, ToroidalCompactificationData.wt, liesIn_iff_of_comp e, r_conj x hσ e]

theorem eigMetAt_conj (hσ : σ' = (starRingEnd ℂ).comp σ) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    (hg : g.IsMap (starRingEnd ℂ) g') (τ : D.host.E →+* ℂ) (R : Option ℝ) :
    (x.eigMetAt σ' R).gram y' g' τ = ((x.eigMetAt σ R).gram y g τ).map (starRingEnd ℂ) := by
  cases R with
  | none => exact hodge_conj x hσ e hg τ
  | some R =>
    simp only [ToroidalCompactificationData.eigMetAt, EigMet.interp]
    rw [wt_conj x hσ e R, hodge_conj x hσ e hg τ, eigMet_conj x e hg τ]
    split_ifs
    exacts [mix_map_conj _ _ _, mixDual_map_conj _ _ _]

end Tor

end GlobalTheory.ShFam.ConjMet

open GlobalTheory.ShFam.ConjMet in

theorem GlobalTheory.ShFam.mets_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ σ' : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ) (p : Pts (Φ.C k).Y σ) (p' : Pts (Φ.C k).Y σ') (a : (Φ.C k).Y.Fnˣ), p'.1 = spMap (starRingEnd ℂ) ≫ p.1 → p ∈ Var.eqnSet σ (divOf (Φ.C k) n) a → (∀ R, Var.Met.h (metsOf x Φ k R σ' n) a p' = Var.Met.h (metsOf x Φ k R σ n) a p) ∧ Var.Met.h (refMet x Φ k σ' n) a p' = Var.Met.h (refMet x Φ k σ n) a p ∧ rFlag x Φ k σ' p' = rFlag x Φ k σ p := by
  intro D A N j S κ s x Φ k σ σ' n p p' a e' ha
  have hσ := embOf_conj (Y := Φ.C k) e'
  have hd := down_conj (Y := Φ.C k) e'
  exact ⟨fun R => met_h_conj e' (fun g g' τ hg => eigMetAt_conj x hσ hd hg τ R) n ha,
    met_h_conj e' (fun g g' τ hg => eigMet_conj x hd hg τ) n ha, r_conj x hσ hd⟩
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_conjugation_symmetry : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ σ' : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ) (p : Pts (Φ.C k).Y σ) (p' : Pts (Φ.C k).Y σ') (a : (Φ.C k).Y.Fnˣ), p'.1 = spMap (starRingEnd ℂ) ≫ p.1 → p ∈ Var.eqnSet σ (divOf (Φ.C k) n) a → (∀ R, Var.Met.h (metsOf x Φ k R σ' n) a p' = Var.Met.h (metsOf x Φ k R σ n) a p) ∧ Var.Met.h (refMet x Φ k σ' n) a p' = Var.Met.h (refMet x Φ k σ n) a p ∧ rFlag x Φ k σ' p' = rFlag x Φ k σ p := by
  first | exact @GlobalTheory.ShFam.mets_conj | exact GlobalTheory.ShFam.mets_conj | (intros; apply GlobalTheory.ShFam.mets_conj <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CombInd

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag)
  (k : s.Comp) (σ : D.what₂.LL →+* ℂ)

theorem metsOf_zero (R R' : Option ℝ) : metsOf x Φ k R σ 0 = metsOf x Φ k R' σ 0 := by
  simp only [metsOf, FlagCpt.met, FlagCpt.genSq, Pi.zero_apply, zpow_zero, Finset.prod_const_one]
  rfl

theorem metsOf_parOf {R : ℝ} {w : Sym D.host.E →₀ ℤ} (hw : ∀ a ∈ w.support, a.2.1 = some R) :
    metsOf x Φ k (parOf w) σ (expo S.Dw w) = metsOf x Φ k (some R) σ (expo S.Dw w) := by
  by_cases h0 : w = 0
  · subst h0
    rw [LineTest.expo_zero]
    exact metsOf_zero x Φ k σ _ _
  · rw [LineTest.parOf_eq h0 hw]

end GlobalTheory.CombInd
end
end
