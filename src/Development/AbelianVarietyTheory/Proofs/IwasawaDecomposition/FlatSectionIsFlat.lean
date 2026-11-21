import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExactStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalFunctionMatrixRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_function_matrix_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (x : ∀ i, Idx Dw τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E) (h : CxFr T.Z σ → ℂ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → (∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) → (∀ a i Q, Per Fu a i Q → h a = perVal c σ τ (x i) (hm i) Q) → LogGrowth h := by
  first | exact @GlobalTheory.ShFam.Hor.logGrowth_of_eq_perVal | exact GlobalTheory.ShFam.Hor.logGrowth_of_eq_perVal | (intros; apply GlobalTheory.ShFam.Hor.logGrowth_of_eq_perVal <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.Chg

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ Xo.XF c}

variable (Z P y) in

def Lifts (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ Z.t.G.left) : Prop :=
  ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
    v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = v ∧
    IsDerivAt0 (fun w => (Fu.ex i P w).left) w (v₀ ≫ Z.m0.toSABMap.φ)

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hy : y ≫ pullback.fst _ _ = Fu.u i P) {x : Sp ℂ ⟶ Z.X} (hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x)

include hP hy hx

theorem exists_dir {v : Sp (DualNumber ℂ) ⟶ Z.t.G.left} (hv : IsTanAtG Z.t x v) : ∃ w, Lifts Z P y w v := by
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [hv.1, ← hx, Category.assoc])
  obtain ⟨w, hw, -⟩ := (isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hy h1).2 ((tan_iff Z.m hx h1).1 hv))
  exact ⟨w, v₀, h1, rfl, hw⟩

theorem eq_sum_of_comb {n : ℕ} {v : Fin n → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)} {W : Fin n → Fin g → ℂ}
    (hW : ∀ k, Lifts Z P y (W k) (v k)) {v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left} {w : Fin g → ℂ} (hw : Lifts Z P y w v')
    {a : Fin n → ℂ} (h : IsCombAtG Z.t x v a v') : w = ∑ k, a k • W k := by
  choose u h1 h2 h3 using hW
  obtain ⟨u', h1', rfl, h3'⟩ := hw
  obtain rfl : v = fun k => u k ≫ Z.m.φ := funext fun k => (h2 k).symm
  have h4 := (comb_iff Z.m0.toSABMap hy h1 a h1').2 ((comb_iff Z.m hx h1 a h1').1 h)
  have h5 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP n _ W h3 a _).1 h4
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  exact (ht.2.2 _ (ht.1 _ _ h3')).unique h3' h5

theorem span_eq_top (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ} (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) :
    ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := ht.2.1 (Pi.basisFun ℂ (Fin g) j)
  have he := (isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ v (e j).1 hv).2 (fun k hk => by
    obtain rfl : k = j := by
      by_contra hne
      exact hk (by simp [hne])
    rfl)
  have htan := ht.1 _ _ hv
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [htan.1, ← hy, Category.assoc])
  obtain ⟨a, ha, -⟩ := f.basis (e j).1 (v₀ ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hy h1).1 htan))
    fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))
  rw [eq_sum_of_comb hP hy hx (W := fun k => W ⟨(e j).1, k⟩) (fun k => hW ⟨_, k⟩) ⟨v₀, h1, rfl, hv⟩ ha]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem linearIndependent (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) : LinearIndependent ℂ W :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (span_eq_top hP hy hx f hW)
    (by rw [← Fintype.card_congr e]; simp)

end GlobalTheory.ShFam.Hor.Chg

namespace GlobalTheory.ShFam.Hor

theorem per_chg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a a' : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)), Per Fu a i Q → a.1 = a'.1 → ∃ Q', Per Fu a' i Q' ∧ ∀ ρ M, Chg a a' ρ M → ∀ v k, Q v ⟨ρ, k⟩ = ∑ j, Q' v ⟨ρ, j⟩ * M j k := by
  rintro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu ⟨x, f⟩ ⟨x', f'⟩ i Q ⟨P, W, y, hP, hy, hyx, hW, hQ⟩ hxx
  obtain rfl : x = x' := hxx
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x.1 ≫ genι Z := by rw [← Category.assoc, hyx]
  choose W' hW' using fun z : Letter Dw => Chg.exists_dir hP hy hx (f'.tan z.1 z.2)
  let b := Module.Basis.mk (Chg.linearIndependent hP hy hx f' hW') (Chg.span_eq_top hP hy hx f' hW')
  let Q' : (Fu.Di i).La →+ (Letter Dw → ℂ) := b.equivFun.toLinearMap.toAddMonoidHom.comp P
  have hQ' : ∀ v, P v = ∑ z, Q' v z • W' z := fun v => by
    have := b.sum_equivFun (P v)
    simp only [b, Module.Basis.coe_mk] at this
    exact this.symm
  refine ⟨Q', ⟨P, W', y, hP, hy, hyx, hW', hQ'⟩, fun ρ M hM v k => ?_⟩
  choose N hN using fun (τ : E →+* ℂ) j => (f.basis τ _ (f'.tan τ j) (f'.eig τ j)).exists
  have hNM : ∀ j, N ρ j = M j := fun j => (f.basis ρ _ (f'.tan ρ j) (f'.eig ρ j)).unique (hN ρ j) (hM.2 j)
  have hc : ∀ τ j, W' ⟨τ, j⟩ = ∑ k, N τ j k • W ⟨τ, k⟩ := fun τ j =>
    Chg.eq_sum_of_comb hP hy hx (W := fun k => W ⟨τ, k⟩) (fun k => hW ⟨τ, k⟩) (hW' ⟨τ, j⟩) (hN τ j)
  have h1 : ∑ z, Q v z • W z = ∑ z : Letter Dw, (∑ j, Q' v ⟨z.1, j⟩ * N z.1 j z.2) • W z := by
    rw [← hQ, hQ', Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [hc, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have h2 := Fintype.linearIndependent_iffₛ.1 (Chg.linearIndependent hP hy hx f hW) _ _ h1 ⟨ρ, k⟩
  simp only [hNM] at h2
  exact h2

end GlobalTheory.ShFam.Hor
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_change_of_eigenFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a a' : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)), Per Fu a i Q → a.1 = a'.1 → ∃ Q', Per Fu a' i Q' ∧ ∀ ρ M, Chg a a' ρ M → ∀ v k, Q v ⟨ρ, k⟩ = ∑ j, Q' v ⟨ρ, j⟩ * M j k := by
  atlas_forward_decl GlobalTheory.ShFam.Hor.per_chg
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locally_holomorphic_periods_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → ∀ b₀ ∈ B, ∃ (B' : Set V) (i : Fin Fu.n) (Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', Per Fu (a b) i (Q b)) ∧ ∀ v z, DifferentiableOn ℂ (fun b => Q b v z) B' := by
  first | exact @GlobalTheory.ShFam.HorLift.exists_hol_per | exact GlobalTheory.ShFam.HorLift.exists_hol_per | (intros; apply GlobalTheory.ShFam.HorLift.exists_hol_per <;> assumption)
end

section
open NumberField

namespace GlobalTheory.ConjugateMultiplicity

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by

  have hsq := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have hprod : H.rt0.re * H.rt0.im = 0 := by linarith [mul_comm H.rt0.re H.rt0.im]
    have him0 : H.rt0.im = 0 := (mul_eq_zero.1 hprod).resolve_left hne
    rw [him0] at hre
    nlinarith [sq_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem emb_rt_sq (H : Host E) (τ : E →+* ℂ) : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
  have h : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h' := congrArg ((↑) : 𝓞 E → E) H.rt_sq
    push_cast at h'
    exact h'
  rw [← map_pow, h, map_neg, map_natCast, H.sqrt_neg_disc_sq]

private theorem mult_conjEmb_eq_ite {H : Host E} (D : Datum H) (τ : E →+* ℂ) :
    Datum.mult D (conjEmb τ) = if τ (H.rt : E) = H.rt0 then Datum.q D else Datum.p D := by

  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have hsq := H.sqrt_neg_disc_sq
    rw [h0] at hsq
    have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
    exact hd (by linear_combination hsq)
  have hc : conjEmb τ (H.rt : E) = starRingEnd ℂ (τ (H.rt : E)) := rfl
  unfold Datum.mult

  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (emb_rt_sq H τ) with h | h
  · have h2 : ¬ conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, rt0_conj_neg_ne_zero]
      exact fun e => hne e.symm
    rw [if_pos h, if_neg h2]
  · have h2 : conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have h3 : ¬ τ (H.rt : E) = H.rt0 := by
      rw [h]
      exact fun e => hne e.symm
    rw [if_pos h2, if_neg h3]

theorem main {H : Host E} (D : Datum H) (τ : E →+* ℂ) :
    Datum.mult D (conjEmb τ) + Datum.mult D τ = Datum.p D + Datum.q D := by
  rw [mult_conjEmb_eq_ite]
  unfold Datum.mult
  split_ifs <;> omega

end GlobalTheory.ConjugateMultiplicity

theorem GlobalTheory.ConjugateMultiplicity.target : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (τ : E →+* ℂ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D τ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.p D + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.q D := by
  intro E _ _ _ H D τ
  rw [GlobalTheory.ConjugateMultiplicity.mult_conjEmb_eq_ite]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
  split_ifs <;> omega
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.PerBasis

theorem mult_conj_add_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (D : Datum H) (τ : E →+* ℂ) : D.mult (conjEmb τ) + D.mult τ = D.p + D.q := by
  first
  | exact @_root_.GlobalTheory.ConjugateMultiplicity.target
  | exact _root_.GlobalTheory.ConjugateMultiplicity.target
  | (apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateMultiplicity.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateMultiplicity.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateMultiplicity.target ..)

theorem exists_indep {E : Type} [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] (J : Type) [Fintype J] (hJ : Fintype.card J = Module.finrank (𝓞 E) M) :
    ∃ x : J → M, LinearIndependent (𝓞 E) x ∧
      ∀ v, ∃ n : ℕ, n ≠ 0 ∧ n • v ∈ Submodule.span (𝓞 E) (Set.range x) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := M) (n := Fintype.card J) hJ.le
  let e := Fintype.equivFin J
  refine ⟨f ∘ e, hf.comp _ e.injective, fun v => ?_⟩
  rw [e.surjective.range_comp]
  have hc : ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Submodule.span (𝓞 E) (Set.range f) := by
    by_contra hcon
    push Not at hcon
    have hli : LinearIndependent (𝓞 E) (Fin.cons v f : Fin (Fintype.card J + 1) → M) := by
      refine LinearIndependent.finCons' v f hf fun c y hy h => ?_
      by_contra hc
      refine hcon c hc ?_
      rw [eq_neg_of_add_eq_zero_left h]
      exact neg_mem hy
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨c, hc0, hc⟩ := hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hd, mul_smul]
    exact Submodule.smul_mem _ _ hc

theorem exists_trace_rep {E : Type} [Field E] [NumberField E] (φ : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ h : E, ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := by
  let ψ : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ fun i => (φ (RingOfIntegers.basis E i) : ℚ)
  have hψ : ∀ a : 𝓞 E, ((φ a : ℤ) : ℚ) = ψ (a : E) := by
    intro a
    have : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ φ =
        (ψ.restrictScalars ℤ) ∘ₗ ((algebraMap (𝓞 E) E).toAddMonoidHom.toIntLinearMap) := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      change ((φ (RingOfIntegers.basis E i) : ℤ) : ℚ) = ψ (algebraMap (𝓞 E) E (RingOfIntegers.basis E i))
      rw [← integralBasis_apply, Module.Basis.constr_basis]
    exact LinearMap.congr_fun this a
  refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm ψ, fun a => ?_⟩
  rw [hψ, mul_comm, ← Algebra.traceForm_apply]
  exact (LinearMap.BilinForm.apply_toDual_symm_apply _ _).symm

theorem exists_isPerBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Di : Datum H) (τ : E →+* ℂ), Di.p = Dw.p ∧ Di.q = Dw.q →
    ∃ (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), IsPerBasis Di x hm := by
  intro E _ _ _ H Dw Di τ ⟨hp, hq⟩
  have := Di.fin
  obtain ⟨x, hx, hsp⟩ := exists_indep (E := E) Di.La (Idx Dw τ) (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, mult_conj_add_mult, Di.rank, hp, hq])
  have hrep : ∀ k k', ∃ h : E, ∀ a : 𝓞 E,
      ((Di.EF (a • x k) (x k') : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h) := fun k k' =>
    exists_trace_rep (AddMonoidHom.toIntLinearMap
      { toFun := fun a : 𝓞 E => Di.EF (a • x k) (x k')
        map_zero' := by simp
        map_add' := fun a b => by simp [add_smul] })
  choose hm hhm using hrep
  refine ⟨x, Matrix.of hm, hx, hsp, fun a k k' => hhm k k' a, fun hdet => ?_⟩
  obtain ⟨c₀, hc₀, hker⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) c₀
  choose c hc using hd
  set v := ∑ k, c k • x k with hv
  have h1 : ∀ (a : 𝓞 E) k', Di.EF (a • v) (x k') = 0 := by
    intro a k'
    have hk := congrFun hker k'
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hk
    have : ((Di.EF (a • v) (x k') : ℤ) : ℚ) = 0 := by
      rw [hv, Finset.smul_sum, map_sum, LinearMap.sum_apply]
      push_cast
      simp_rw [← mul_smul, hhm]
      rw [← map_sum]
      have : ∑ k, ((a * c k : 𝓞 E) : E) * hm k k' = (a : E) * ((d : 𝓞 E) : E) * ∑ k, c₀ k * hm k k' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h2 : ((c k : 𝓞 E) : E) = ((d : 𝓞 E) : E) * c₀ k := by
          exact (hc k).trans (Algebra.smul_def _ _)
        have h3 : ((a * c k : 𝓞 E) : E) = (a : E) * ((c k : 𝓞 E) : E) := map_mul (algebraMap (𝓞 E) E) _ _
        rw [h3, h2]; ring
      rw [this, hk]; simp
    exact_mod_cast this
  have h2 : ∀ w ∈ Submodule.span (𝓞 E) (Set.range x), ∀ a : 𝓞 E, Di.EF v (a • w) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k, rfl⟩ := hw
      intro a
      have := h1 (H.bar.symm a) k
      rwa [Di.adj, RingEquiv.apply_symm_apply] at this
    | zero => simp
    | add y z _ _ hy hz => intro a; rw [smul_add, map_add, hy, hz, add_zero]
    | smul b y _ hy => intro a; rw [← mul_smul, hy]
  have h3 : v = 0 := by
    apply Di.unimod.1
    rw [map_zero]
    ext w
    obtain ⟨n, hn, hw⟩ := hsp w
    have := h2 _ hw 1
    rw [one_smul, map_nsmul] at this
    simpa [hn] using this
  apply hc₀
  funext k
  have h4 := Fintype.linearIndependent_iff.1 hx c h3 k
  have h5 := hc k
  rw [h4, map_zero, Algebra.smul_def] at h5
  refine (mul_eq_zero.1 h5.symm).resolve_left ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.coe_ne_zero d)

end GlobalTheory.ShFam.Hor.PerBasis
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Di : Datum H) (τ : E →+* ℂ), Di.p = Dw.p ∧ Di.q = Dw.q → ∃ (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), IsPerBasis Di x hm := by
  first | exact @GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis | exact GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis | (intros; apply GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_divOf_ne_bot_of_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ) (h : CxFr Z σ → ℂ), τ (H.rt : E) = H.rt0 → HorFn τ h → (C.Y.H0 (divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥ ∧ C.Y.H0 (-divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥) := by
  first | exact @GlobalTheory.ShFam.Hor.Sec.H0_ne_bot_of_horFn | exact GlobalTheory.ShFam.Hor.Sec.H0_ne_bot_of_horFn | (intros; apply GlobalTheory.ShFam.Hor.Sec.H0_ne_bot_of_horFn <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

section Lin

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem det_fromRows_mul (A : Matrix m m ℂ) (B : Matrix n n ℂ) (R : Matrix m (m ⊕ n) ℂ) (C : Matrix n (m ⊕ n) ℂ) :
    (Matrix.fromRows (A * R) (B * C)).det = A.det * B.det * (Matrix.fromRows R C).det := by
  rw [← Matrix.det_fromBlocks_zero₂₁ A 0 B, ← Matrix.det_mul, Matrix.fromBlocks_mul_fromRows]
  simp

theorem horVal_change {K : Matrix (m ⊕ n) m ℂ} {C : Matrix n (m ⊕ n) ℂ} {R : Matrix m (m ⊕ n) ℂ}
    {S S' : Matrix (m ⊕ n) n ℂ} (N : Matrix m m ℂ) (M : Matrix n n ℂ) (h : C * K = 0) (hS : C * S = 1)
    (hR : R * (K * N) = 1) (hS' : Mᵀ * C * S' = 1) :
    horVal K C * M.det = horVal (K * N) (Mᵀ * C) * N.det := by
  have h1 : N * R * K = 1 := by
    rw [Matrix.mul_assoc, mul_eq_one_comm, Matrix.mul_assoc]; exact hR
  have h2 : Mᵀ * C * (K * N) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h]; simp
  have e1 := det_fromRows_mul N 1 R C
  have e2 := det_fromRows_mul 1 Mᵀ R C
  rw [Matrix.one_mul] at e1 e2
  rw [horVal_eq h h1 hS, horVal_eq h2 hR hS', e1, e2]
  simp only [Matrix.det_one, Matrix.det_transpose]
  ring

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem differentiableAt_det {A : V → Matrix m m ℂ} {b : V} (h : ∀ i j, DifferentiableAt ℂ (fun b => A b i j) b) :
    DifferentiableAt ℂ (fun b => (A b).det) b := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun s _ => (differentiableAt_const _).mul ?_
  exact (HasFDerivAt.finset_prod fun i _ => (h _ _).hasFDerivAt).differentiableAt

theorem differentiableAt_horVal {K : V → Matrix (m ⊕ n) m ℂ} {C : V → Matrix n (m ⊕ n) ℂ} {b₀ : V}
    (hK : ∀ i j, DifferentiableAt ℂ (fun b => K b i j) b₀) (hC : ∀ i j, DifferentiableAt ℂ (fun b => C b i j) b₀)
    {R : Matrix m (m ⊕ n) ℂ} (hR : R * K b₀ = 1)
    (h : ∀ᶠ b in 𝓝 b₀, C b * K b = 0 ∧ ∃ S : Matrix (m ⊕ n) n ℂ, C b * S = 1) :
    DifferentiableAt ℂ (fun b => horVal (K b) (C b)) b₀ := by
  have d1 : DifferentiableAt ℂ (fun b => (R * K b).det) b₀ := differentiableAt_det fun i j => by
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hK _ _)
  have d2 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det) b₀ := differentiableAt_det fun i j => by
    rcases i with i | i
    · exact differentiableAt_const _
    · exact hC i j
  have n1 : (R * K b₀).det ≠ 0 := by rw [hR]; simp
  have d3 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det * ((R * K b).det)⁻¹) b₀ :=
    d2.fun_mul (d1.fun_inv n1)
  refine d3.congr_of_eventuallyEq ?_
  filter_upwards [h, d1.continuousAt.eventually_ne n1] with b ⟨h0, S, hS⟩ hb
  have hu : IsUnit (R * K b).det := hb.isUnit
  have e := det_fromRows_mul (R * K b)⁻¹ 1 R (C b)
  rw [Matrix.one_mul] at e
  rw [horVal_eq h0 (R := (R * K b)⁻¹ * R) (by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]) hS, e,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_one]
  ring

end Lin

theorem exists_generates {F : Type} [Field F] (Y : GlobalTheory.ProjVar.Var F) (D : Y.Dv) (h : Y.H0 D ≠ ⊥)
    (h' : Y.H0 (-D) ≠ ⊥) : ∃ s, ∀ y, D.GeneratesAt y s := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h'
  have hst : s * t ∈ Y.H0 0 := add_neg_cancel D ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hs ht
  let L : Y.H0 0 →ₗ[F] Y.H0 0 := (LinearMap.mulLeft F (s * t)).restrict fun g hg =>
    add_zero (0 : Y.Dv) ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hst hg
  have hinj : Function.Injective L := fun a b e =>
    Subtype.ext (mul_left_cancel₀ (mul_ne_zero hs0 ht0) (congrArg Subtype.val e))
  obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨1, GlobalTheory.ProjVar.Var.eff_iff_one_mem.1 Y.eff_zero⟩
  have hu' : s * t * u = 1 := congrArg Subtype.val hu
  refine ⟨s, fun y => ?_⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have r1 := hg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hs y)
  have r2 := hg.neg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 ht y)
  have r3 := CartierDiv.regularAt_zero_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 u.2 y)
  refine hg.generatesAt_iff.2 ((unitAt_iff (mul_ne_zero hs0 g.ne_zero)).2 ⟨r1, ?_⟩)
  have e : (s * (g : Y.Fn))⁻¹ = t * ((g⁻¹ : Y.Fnˣ) : Y.Fn) * u := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hu', Units.val_inv_eq_inv_val]
    have := g.ne_zero
    field_simp
  exact e ▸ r2.mul r3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {σ : c.F →+* ℂ}
  {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {τ : E →+* ℂ} {x : ∀ i, Idx Dw τ → (Fu.Di i).La}
  {hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E}

theorem horOf_eq {Z : Model Xo c β} (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) (hx : ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i))
    (a : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (h : Per Fu a i Q) :
    horOf Fu τ x hm a = perVal c σ τ (x i) (hm i) Q := by
  have hex : ∃ iQ : Σ i : Fin Fu.n, (Fu.Di i).La →+ (Letter Dw → ℂ), Per Fu a iQ.1 iQ.2 := ⟨⟨i, Q⟩, h⟩
  rw [horOf, dif_pos hex]
  have hs := hex.choose_spec
  generalize hex.choose = w at hs
  obtain ⟨j, Q'⟩ := w
  obtain rfl : j = i := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).1 _ _ _ _ hs h
  obtain ⟨gm, h1, h2, h3⟩ := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).2 _ _ _ h hs
  have := (GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one E H Dw l c σ _ τ (x j) (hm j) Q' gm (hx j) (GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β Z σ g e Fu τ a j Q' _ _ hs (hx j))
    h1).2.2 hl h2
  rw [← this]
  congr 1
  exact AddMonoidHom.ext h3

theorem horFn_horOf {Y : Model Xo c β} (T : TorModel Y) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hr : 1 ≤ Dw.p + Dw.q)
    (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) (hx : ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) :
    HorFn (Z := T.Z) τ (horOf Fu τ x hm) := by
  have good := fun a i Q h => GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β T.Z σ g e Fu τ a i Q _ _ h (hx i)
  refine ⟨fun a ha => ?_, fun a a' M N ha hM hN => ?_, fun V _ _ _ B a hB hf hi b₀ hb => ?_,
    GlobalTheory.T.horizontal_function_matrix_relation E H Dw l Xo c O β Y T σ g e Fu τ x hm _ hσ hr hx (horOf_eq hl hx)⟩
  · obtain ⟨i, Q, h⟩ := GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β T.Z σ g e Fu a ha
    rw [horOf_eq hl hx a i Q h]
    exact (good a i Q h).perVal_ne_zero
  · obtain ⟨i, Q, h⟩ := GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β T.Z σ g e Fu a ha
    obtain ⟨Q', h', hc⟩ := GlobalTheory.T.periods_change_of_eigenFrame E H Dw l Xo c O β T.Z σ g e Fu a a' i Q h hM.1
    have key : ∀ ρ M, Chg a a' ρ M → perMat (x i) Q ρ = Mᵀ * perMat (x i) Q' ρ := fun ρ M hM => by
      ext j k
      simp only [perMat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hc ρ M hM, mul_comm]
    have k2 : kerMat c σ τ (x i) (hm i) Q = kerMat c σ τ (x i) (hm i) Q' * N := by
      rw [kerMat, key _ _ hN, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, kerMat]
    obtain ⟨-, -, ⟨R, hR⟩, S, hS⟩ := good a i Q h
    obtain ⟨-, h0, -, S', hS'⟩ := good a' i Q' h'
    rw [horOf_eq hl hx a i Q h, horOf_eq hl hx a' i Q' h', perVal, perVal, k2, key _ _ hM]
    exact horVal_change N M h0 hS' (k2 ▸ hR) (key _ _ hM ▸ hS)
  · obtain ⟨B', i, Q, hB', hb', -, hP, hd⟩ := GlobalTheory.T.exists_locally_holomorphic_periods_family E H Dw l Xo c O β T.Z σ g e Fu V B a hB hf hi b₀ hb
    have hn := hB'.mem_nhds hb'
    have hd' : ∀ v z, DifferentiableAt ℂ (fun b => Q b v z) b₀ := fun v z => (hd v z).differentiableAt hn
    obtain ⟨R, hR⟩ := (good _ i _ (hP b₀ hb')).2.2.1
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.congr_of_eventuallyEq
      (differentiableAt_horVal (K := fun b => kerMat c σ τ (x i) (hm i) (Q b)) (C := fun b => perMat (x i) (Q b) τ)
        (fun j k => ?_) (fun j k => hd' _ _) hR ?_) ?_)
    · simp only [kerMat, Matrix.mul_apply]
      exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hd' _ _)
    · filter_upwards [hn] with b hb
      exact ⟨(good _ i _ (hP b hb)).2.1, (good _ i _ (hP b hb)).2.2.2⟩
    · filter_upwards [hn] with b hb
      exact horOf_eq hl hx _ i _ (hP b hb)

end GlobalTheory.ShFam.Hor

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
  Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo in

theorem GlobalTheory.ShFam.Hor.isFlat_flatSec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag) (k : s.Comp) (τ : D.what₂.Tau), IsFlat (fl.C k) (DV.tauEmb D τ) (flatSec s fl k τ) := by
  intro D A N j S κ s fl k τ
  have hσ : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl
  obtain ⟨g, e, Fu, -⟩ := (s.unf κ.σ₀ hσ).1.2.2.2.2.2
  choose x hm hx using fun i : Fin Fu.n =>
    GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature _ A.H S.Dw (Fu.Di i) (DV.tauEmb D τ) (Fu.sig i)
  have hr : 1 ≤ S.Dw.p + S.Dw.q := by have := S.two_le; have := S.rank_eq; omega
  obtain ⟨h1, h2⟩ := GlobalTheory.T.H0_divOf_ne_bot_of_horFn _ A.H S.Dw κ.l _ κ.c _ _ s.T.Z κ.σ₀ _ κ.e (fl.C k) (DV.tauEmb D τ) _ (A.cm τ)
    (GlobalTheory.ShFam.Hor.horFn_horOf (Fu := Fu) s.T hσ hr κ.good hx)
  exact Classical.epsilon_spec (GlobalTheory.ShFam.Hor.exists_generates _ _ h1 h2)
end
end
