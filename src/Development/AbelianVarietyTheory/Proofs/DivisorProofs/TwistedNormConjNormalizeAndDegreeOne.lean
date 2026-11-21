import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConj
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedNormProductIterate_twistedConj : ∀ {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ g : H), nrmG θ r (g⁻¹ * δ * θ g) = g⁻¹ * nrmG θ r δ * (⇑θ)^[r] g ∧ δ * θ (nrmG θ r δ) = nrmG θ r δ * (⇑θ)^[r] δ := by
  first | (exact @GlobalTheory.LKMid.nrmG_twConj) | (exact GlobalTheory.LKMid.nrmG_twConj) | (intros; apply GlobalTheory.LKMid.nrmG_twConj  <;> assumption)
end

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKResNrmConj

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem coe_frobQ_iterate (r k : ℕ) (b : Qr p r) :
    (((⇑(frobQ p r))^[k] b : Qr p r) : PadicAlgCl p) = (frobK p (Q0 p) ^ k) (b : PadicAlgCl p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
    rfl

theorem frobQ_iterate_self (r : ℕ) (hr : 0 < r) (b : Qr p r) : (⇑(frobQ p r))^[r] b = b := by
  refine Subtype.ext ?_
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  rw [coe_frobQ_iterate]
  exact (IsFrobOn.pow_fixes_iff p (Q0 p) hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ b.2

theorem sigKQ_iterate_self (r : ℕ) (hr : 0 < r) (y : KQ p K r) : (⇑(sigKQ p K r))^[r] y = y := by
  have ht : ∀ (k : ℕ) (a : K) (b : Qr p r), (⇑(sigKQ p K r))^[k] (inclK p K r a * inclQ p K r b) =
      inclK p K r a * inclQ p K r ((⇑(frobQ p r))^[k] b) := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, sigKQ_apply_inclK, sigKQ_apply_inclQ,
        Function.iterate_succ_apply']
  have key : ∀ z : K ⊗[ℚ_[p]] Qr p r, (⇑(sigKQ p K r))^[r] (z : KQ p K r) = (z : KQ p K r) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact iterate_map_zero (sigKQ p K r) r
    | tmul a b =>
      have e : inclK p K r a * inclQ p K r b = (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) := by
        change (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] b) = a ⊗ₜ[ℚ_[p]] b
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have h := ht r a b
      rw [frobQ_iterate_self p r hr, e] at h
      exact h
    | add z w hz hw =>
      exact (iterate_map_add (sigKQ p K r) r (z : KQ p K r) (w : KQ p K r)).trans (congrArg₂ (· + ·) hz hw)
  exact key y

theorem sigRes_iterate_self (n r : ℕ) (hr : 0 < r) (g : GL (Fin n) (KQ p K r)) :
    (⇑(sigRes p K n r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin n), ((⇑(sigRes p K n r))^[k] g).val i j = (⇑(sigKQ p K r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, sigKQ_iterate_self p K r hr]

end GlobalTheory.LKResNrmConj
end

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem frobQ_fixed_mem (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r) (b : Qr p r) (hb : frobQ p r b = b) :
    ∃ c : ℚ_[p], algebraMap ℚ_[p] (Qr p r) c = b := by
  have h1 : frobK p (Q0 p) (b : PadicAlgCl p) = b := congrArg Subtype.val hb
  have h2 : (b : PadicAlgCl p) ∈ Q0 p := mem_of_frobK_fixed inferInstance (Kn_le_Kur hr b.2) h1
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 h2
  exact ⟨c, Subtype.ext hc⟩

theorem sigKQ_fixed_eq_inclK : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r →
    ∀ x : GlobalTheory.LKRes.KQ p K r, GlobalTheory.LKRes.sigKQ p K r x = x → ∃ a : K, GlobalTheory.LKRes.inclK p K r a = x := by
  intro p _ K r hr
  change ∀ x : K ⊗[ℚ_[p]] Qr p r, Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) x = x →
    ∃ a : K, (Algebra.TensorProduct.includeLeft : K →ₐ[ℚ_[p]] K ⊗[ℚ_[p]] Qr p r) a = x
  intro x hx
  let f : ℚ_[p] →ₗ[ℚ_[p]] Qr p r := Algebra.linearMap _ _
  let g : Qr p r →ₗ[ℚ_[p]] Qr p r := (frobQ p r).toLinearMap - LinearMap.id
  have hex : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      have hb' : frobQ p r b = b := sub_eq_zero.1 hb
      exact frobQ_fixed_mem p r hr b hb'
    · rintro ⟨c, rfl⟩
      simp [g, f]
  have hex2 := Module.Flat.lTensor_exact K hex
  have hg : g.lTensor K =
      (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)).toLinearMap - LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    simp [g, TensorProduct.tmul_sub]
  have hx0 : g.lTensor K x = 0 := by
    rw [hg, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply]
    exact sub_eq_zero.2 hx
  obtain ⟨y, hy⟩ := (hex2 x).1 hx0
  refine ⟨TensorProduct.rid ℚ_[p] K y, ?_⟩
  rw [← hy]
  clear hy hx hx0
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [TensorProduct.rid_tmul, LinearMap.lTensor_tmul, f, Algebra.linearMap_apply]
    change (c • a) ⊗ₜ[ℚ_[p]] (1 : Qr p r) = a ⊗ₜ[ℚ_[p]] (algebraMap ℚ_[p] (Qr p r) c)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv, map_add]

end GlobalTheory.LKRes
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem iterate_fst (G : HTGroup p) (r k : ℕ) (g : Gr G r) :
    ((⇑(sigG G r))^[k] g).1 = (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem iterate_snd (G : HTGroup p) (r k : ℕ) (g : Gr G r) (i : Fin G.m) :
    ((⇑(sigG G r))^[k] g).2 i = (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem unramifiedExtFrobeniusGL_one_iterate_degree (r : ℕ) (hr : 0 < r) (g : GL (Fin 1) (Qr p r)) :
    (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin 1), ((⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g).val i j
      = (⇑(frobQ p r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, GlobalTheory.LKResNrmConj.frobQ_iterate_self p r hr]

theorem inclK_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    Function.Injective (inclK p K r) :=
  Algebra.TensorProduct.includeLeft_injective (S := ℚ_[p]) (algebraMap ℚ_[p] (Qr p r)).injective

theorem iterate_self (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · rw [iterate_fst, unramifiedExtFrobeniusGL_one_iterate_degree r hr]
  · rw [iterate_snd, GlobalTheory.LKResNrmConj.sigRes_iterate_self p (G.Fw i) G.n r hr]

theorem fix_incl (G : HTGroup p) (r : ℕ) (γ : Gp G) : sigG G r (inclG G r γ) = inclG G r γ := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change frobQ p r (((inclG G r γ).1 : Matrix (Fin 1) (Fin 1) (Qr p r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe]
    by_cases h : a = b
    · subst h; simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h]
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change sigKQ p (G.Fw i) r (((inclG G r γ).2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_snd, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact sigKQ_apply_inclK p (G.Fw i) r _

end GlobalTheory.LKMid.SigIter

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem incl_injective (G : HTGroup p) (r : ℕ) : Function.Injective (inclG G r) := by
  intro γ γ' h
  have h1 := congrArg (fun g : Gr G r => ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) h
  have h2 := fun i (a b : Fin G.n) =>
    congrArg (fun g : Gr G r => ((g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) h
  simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
    MonoidHom.coe_coe, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.diagonal_apply_eq] at h1 h2
  refine Prod.ext (Units.ext ((algebraMap ℚ_[p] (Qr p r)).injective h1)) (funext fun i => ?_)
  exact Units.ext (Matrix.ext fun a b => inclK_injective (G.Fw i) r (h2 i a b))

theorem fixed_mem_range (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) (hg : sigG G r g = g) :
    g ∈ (inclG G r).range := by
  have hf : frobQ p r ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) = (g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 :=
    congrArg (fun x : Gr G r => ((x.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) hg
  obtain ⟨c, hc⟩ := frobQ_fixed_mem p r hr _ hf
  have hdet1 : IsUnit ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) := by
    have := Matrix.isUnits_det_units g.1
    rwa [Matrix.det_fin_one] at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact not_isUnit_zero (hc ▸ hdet1)
  have hfix : ∀ i (a b : Fin G.n), ∃ x : G.Fw i,
      inclK p (G.Fw i) r x = (g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b := fun i a b =>
    sigKQ_fixed_eq_inclK p (G.Fw i) r hr _
      (congrArg (fun x : Gr G r => ((x.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) hg)
  choose M hM using hfix
  have hmap : ∀ i, (Matrix.of (M i)).map (inclK p (G.Fw i) r) = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
    fun i => Matrix.ext fun a b => hM i a b
  have hdet : ∀ i, (Matrix.of (M i)).det ≠ 0 := by
    intro i h0
    have e := RingHom.map_det (inclK p (G.Fw i) r).toRingHom (Matrix.of (M i))
    rw [h0, map_zero, RingHom.mapMatrix_apply] at e
    have e' : (Matrix.of (M i)).map (inclK p (G.Fw i) r).toRingHom = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
      hmap i
    rw [e'] at e
    have hu := Matrix.isUnits_det_units (g.2 i)
    rw [← e] at hu
    have hsub : Subsingleton (KQ p (G.Fw i) r) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
    have := inclK_injective (G.Fw i) r (Subsingleton.elim (inclK p (G.Fw i) r 1) (inclK p (G.Fw i) r 0))
    exact one_ne_zero this
  refine ⟨(Units.mk0 c hc0, fun i => GeneralLinearGroup.mkOfDetNeZero (Matrix.of (M i)) (hdet i)), ?_⟩
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (funext fun i => Units.ext ?_)
  · have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe, Matrix.diagonal_apply_eq, Units.val_mk0]
    exact hc
  · rw [← hmap i]
    rfl

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
    (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧
      Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range :=
  fun _ _ G r hr => ⟨iterate_self G r hr, fix_incl G r, incl_injective G r, fixed_mem_range G r hr⟩

end GlobalTheory.LKMid.SigIter

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧ Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range := GlobalTheory.LKMid.SigIter.main
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧ Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range := by
  first | (exact @GlobalTheory.LKMid.SigIter.main) | (exact GlobalTheory.LKMid.SigIter.main) | (intros; apply GlobalTheory.LKMid.SigIter.main  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem nrm_exact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), (∀ (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r →
    IsNrm G r γ δ z → IsNrm G r γ (z * δ * (sigG G r z)⁻¹) 1) ∧ ∀ γ : Gp G, IsNrm G 1 γ (inclG G 1 γ) 1 := by
  intro p _ G
  refine ⟨fun r γ δ z hr h => ?_, fun γ => ?_⟩
  · unfold IsNrm at h ⊢
    have e := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ z⁻¹).1
    have hit := (GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr).1 z⁻¹
    rw [inv_inv] at e
    rw [← map_inv, e, h, hit]
    group
  · unfold IsNrm nrmG
    simp
end GlobalTheory
end
