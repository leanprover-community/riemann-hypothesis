import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.EllipticCentralizerQuotientCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MeasurePrjFPreimage

section
noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

section Bridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def evInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    (Pi.evalRingHom (fun w : InfinitePlace X.B.I.F => w.Completion) v)

def thetaInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E →+* ℂ :=
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  (Algebra.TensorProduct.lift
    ({ evInf X v with commutes' := fun a => evV_algebraMap X.B.I v a } : Ainf X.B.I.F →ₐ[X.B.I.F] ℂ)
    ({ X.B.I.φ v with commutes' := X.B.I.φ_over v } : X.B.I.E →ₐ[X.B.I.F] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem thetaV_eq (v : InfinitePlace X.B.I.F) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    thetaV X.B.I v y = thetaInf X v (tensMap (E := X.B.I.E) (fstA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [thetaV_tmul]
    simp only [thetaInf, tensMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ofHAInf_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).1 = (splitA X.B.I.cm.sig X.B.I.J b).1) :
    ofHAInf X.B.I a = ofHAInf X.B.I b := by
  funext v
  unfold ofHAInf
  congr 2
  ext i j
  simp only [Matrix.map_apply, thetaV_eq]
  have := congrArg (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (thetaInf X v) this

theorem ofHAFin_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).2 = (splitA X.B.I.cm.sig X.B.I.J b).2) :
    ofHAFin X.B.I a = ofHAFin X.B.I b := by
  unfold ofHAFin
  ext i j
  simp only [Matrix.map_apply, tauF_eq_comm]
  have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E) this

theorem eq_of_ofHA (p q : X.B.I.GA) (h1 : ofHAInf X.B.I (toHA X.B.I hb p) = ofHAInf X.B.I (toHA X.B.I hb q))
    (h2 : ofHAFin X.B.I (toHA X.B.I hb p) = ofHAFin X.B.I (toHA X.B.I hb q)) : p = q := by
  obtain ⟨a₁, b₁⟩ := (toHA_isBridge X.B.I hb) p
  obtain ⟨a₂, b₂⟩ := (toHA_isBridge X.B.I hb) q
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((a₁ v).trans ((congrFun h1 v).trans (a₂ v).symm)))
  · exact Subtype.ext (Units.ext (b₁.trans (h2.trans b₂.symm)))

theorem toInf_mul (s t : X.B.I.Ginf) : X.toInf hb (s * t) = X.toInf hb s * X.toInf hb t := by
  unfold HidaSetting.toInf
  rw [show ((s * t, 1) : X.B.I.GA) = (s, 1) * (t, 1) by simp, map_mul, map_mul]
  rfl

theorem toHA_inf_one (hS : SplitIso) (x : X.B.I.Gf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, x))).1 = 1 := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  set h := toHA X.B.I hb (1, x) with hh
  set h' := e.symm (1, (splitA X.B.I.cm.sig X.B.I.J h).2) with hh'
  have hs' : splitA X.B.I.cm.sig X.B.I.J h' = (1, (splitA X.B.I.cm.sig X.B.I.J h).2) := by
    have h0 := e.apply_symm_apply (1, (splitA X.B.I.cm.sig X.B.I.J h).2)
    rw [he] at h0
    exact h0
  set q := (toHA X.B.I hb).symm h' with hq
  have hqh : toHA X.B.I hb q = h' := (toHA X.B.I hb).apply_symm_apply h'
  have h1 : ofHAInf X.B.I (toHA X.B.I hb q) = ofHAInf X.B.I (toHA X.B.I hb (1, 1)) := by
    rw [hqh]
    apply ofHAInf_congr
    rw [hs', show ((1, 1) : X.B.I.GA) = 1 from rfl, map_one, map_one]
    rfl
  have h1' : ofHAInf X.B.I (toHA X.B.I hb (1, 1)) = ofHAInf X.B.I (toHA X.B.I hb (1, x)) := by
    obtain ⟨a₁, -⟩ := (toHA_isBridge X.B.I hb) (1, 1)
    obtain ⟨a₂, -⟩ := (toHA_isBridge X.B.I hb) (1, x)
    funext v
    exact (a₁ v).symm.trans (a₂ v)
  have h2 : ofHAFin X.B.I (toHA X.B.I hb q) = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := by
    rw [hqh]
    apply ofHAFin_congr
    rw [hs']
  have hq1 : q = (1, x) := eq_of_ofHA X hb q (1, x) (h1.trans h1') h2
  have : h' = h := by rw [← hqh, hq1]
  rw [← this, hs']

theorem split_toHA (hS : SplitIso) (p : X.B.I.GA) :
    splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (X.toInf hb p.1, finHA X hb p.2) := by
  have e : p = (p.1, 1) * (1, p.2) := by simp
  conv_lhs => rw [e, map_mul, map_mul]
  refine Prod.ext ?_ ?_
  · show X.toInf hb p.1 * (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, p.2))).1 = _
    rw [toHA_inf_one X hb hS, mul_one]
  · show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (p.1, 1))).2 * finHA X hb p.2 = _
    rw [toHA_fin_one X hb, one_mul]

theorem toInf_surjective (hS : SplitIso) : Function.Surjective (X.toInf hb) := by
  intro y
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  set p := (toHA X.B.I hb).symm (e.symm (y, 1))
  have hp : splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (y, 1) := by
    rw [← he]
    simp [p]
  have h2 : p.2 = 1 := eq_one_of_toHA_fin X hb p (by rw [hp])
  refine ⟨p.1, ?_⟩
  have := congrArg Prod.fst hp
  rw [split_toHA X hb hS] at this
  exact this

end Bridge

end MassDataMassesW
end
end

section
noncomputable section

open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NRatW

section Gen

variable {E S : Type} [Field E] [CommRing S] (ψ : E →+* S) {n r : ℕ}

theorem up_span (e : Fin r → Fin n → E) (s : Set (Fin r)) {w : Fin n → E}
    (hw : w ∈ Submodule.span E (e '' s)) :
    (fun i => ψ (w i)) ∈ Submodule.span S ((fun b i => ψ (e b i)) '' s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  | zero =>
    have : (fun i => ψ ((0 : Fin n → E) i)) = 0 := by funext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun i => ψ ((x + y) i)) = (fun i => ψ (x i)) + (fun i => ψ (y i)) := by funext i; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : (fun i => ψ ((c • x) i)) = ψ c • (fun i => ψ (x i)) := by funext i; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

theorem map_sub_one_mulVec (M : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (M.map ψ - 1) *ᵥ (fun i => ψ (x i)) = fun i => ψ (((M - 1) *ᵥ x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  have h : (M - 1).map ψ = M.map ψ - 1 := by
    ext a b
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, map_sub]
    split_ifs <;> simp
  rw [h]
  rfl

theorem down_span (hψ : Function.Injective ψ) (e K : Fin r → Fin n → E)
    (hK : ∀ c b, ∑ j, K c j * e b j = if c = b then 1 else 0) (s : Set (Fin r)) (w : Fin n → E)
    (hw : (fun i => ψ (w i)) ∈ Submodule.span S ((fun b i => ψ (e b i)) '' s)) :
    w ∈ Submodule.span E (e '' s) := by
  classical
  set T := Finset.univ.filter (fun b => b ∈ s) with hT
  have key : ∀ x ∈ Submodule.span S ((fun b i => ψ (e b i)) '' s),
      x = ∑ b ∈ T, (∑ j, ψ (K b j) * x j) • (fun i => ψ (e b i)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      have h1 : ∀ b, (∑ j, ψ (K b j) * ψ (e c j)) = if b = c then 1 else 0 := by
        intro b
        have := congrArg ψ (hK b c)
        simp only [map_sum, map_mul] at this
        rw [this]; split_ifs <;> simp
      simp only [h1, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_eq' T c]
      rw [if_pos (by simp [hT, hc])]
    | zero => simp
    | add x y _ _ hx hy =>
      conv_lhs => rw [hx, hy]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← add_smul]
      congr 1
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    | smul c x _ hx =>
      conv_lhs => rw [hx]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul]
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
  have h := key _ hw
  have h2 : (fun i => ψ (w i)) = fun i => ψ ((∑ b ∈ T, (∑ j, K b j * w j) • e b) i) := by
    rw [h]
    funext i
    simp [Finset.sum_apply, map_sum, map_mul]
  have h3 : w = ∑ b ∈ T, (∑ j, K b j * w j) • e b := by
    funext i
    exact hψ (congrFun h2 i)
  rw [h3]
  refine Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
  simpa [hT] using hb

theorem perp_up (M : Matrix (Fin n) (Fin n) E) (e f K : Fin r → Fin n → E)
    (hKf : ∀ a b, ∑ j, K a j * f b j = if a = b then 1 else 0)
    (hrat : ∀ y : Fin n → E, (∀ a, ∑ j, K a j * y j = 0) →
      (M - 1) *ᵥ y ∈ Submodule.span E (Set.range e))
    (y : Fin n → S) (hy : ∀ a, ∑ j, ψ (K a j) * y j = 0) :
    (M.map ψ - 1) *ᵥ y ∈ Submodule.span S (Set.range fun b i => ψ (e b i)) := by
  classical
  set p : Fin n → Fin n → E := fun j => Pi.single j 1 - ∑ b, K b j • f b with hp
  have hpK : ∀ j a, ∑ i, K a i * p j i = 0 := by
    intro j a
    simp only [hp, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 : ∑ i, K a i * (Pi.single j (1 : E) : Fin n → E) i = K a j := by
      simp [Pi.single_apply]
    have h2 : ∑ b, ∑ i, K a i * (K b j * f b i) = K a j := by
      have : ∀ b, ∑ i, K a i * (K b j * f b i) = K b j * (if a = b then 1 else 0) := by
        intro b
        rw [← hKf a b, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [h1, h2, sub_self]
  have hy' : y = ∑ j, y j • (fun i => ψ (p j i)) := by
    funext i
    simp only [hp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, map_sub, map_sum, map_mul,
      mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have h1 : ∑ j, y j * ψ ((Pi.single j (1 : E) : Fin n → E) i) = y i := by
      simp [Pi.single_apply]
    have h2 : ∑ j, ∑ b, y j * (ψ (K b j) * ψ (f b i)) = 0 := by
      rw [Finset.sum_comm]
      have : ∀ b, ∑ j, y j * (ψ (K b j) * ψ (f b i)) = (∑ j, ψ (K b j) * y j) * ψ (f b i) := by
        intro b
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      simp only [this, hy, zero_mul, Finset.sum_const_zero]
    rw [h1, h2, sub_zero]
  rw [hy', Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Matrix.mulVec_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [map_sub_one_mulVec]
  have := up_span ψ e Set.univ (w := (M - 1) *ᵥ p j) (by rw [Set.image_univ]; exact hrat _ (hpK j))
  rwa [Set.image_univ] at this

end Gen

end MassDataMassesW.NRatW
end
end

section
noncomputable section

open scoped TensorProduct
open Matrix NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

namespace MassDataMassesW.NRatW

def RatN {E : Type} [Field E] {n r : ℕ} (e K : Fin r → Fin n → E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a : Fin r, (M - 1) *ᵥ e a ∈ Submodule.span E (e '' {b | b < a})) ∧
  ∀ y : Fin n → E, (∀ a, ∑ j, K a j * y j = 0) → (M - 1) *ᵥ y ∈ Submodule.span E (Set.range e)

section Spec

variable {D : D7} (X : HidaSetting D)

def Kf {r : ℕ} (x : Fin r → Fin X.B.I.n → X.B.I.E) : Fin r → Fin X.B.I.n → X.B.I.E :=
  fun a j => ∑ i, star (x a i) * X.B.I.J i j

theorem Kf_apply {r : ℕ} (x : Fin r → Fin X.B.I.n → X.B.I.E) (a : Fin r) (y : Fin X.B.I.n → X.B.I.E) :
    ∑ j, Kf X x a j * y j = hE X.B.I.cm.sig X.B.I.J (x a) y := by
  simp only [Kf, hE, Formalism.UG.hform, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem hE_swap (x y : Fin X.B.I.n → X.B.I.E) :
    hE X.B.I.cm.sig X.B.I.J x y = star (hE X.B.I.cm.sig X.B.I.J y x) := by
  have hJ : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := by
    intro i j
    have := congrFun (congrFun X.B.I.J_herm i) j
    simpa [Formalism.UG.cT, starRingEnd_apply] using this
  show (∑ i, ∑ j, star (x i) * X.B.I.J i j * y j) = star (∑ i, ∑ j, star (y i) * X.B.I.J i j * x j)
  rw [star_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul, star_mul, star_star, hJ]
  ring

theorem std (u : D.what₂.Word) : (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) :=
  MassDataLevelSSteps.FrameW.frameOf_isStd X u

theorem hKf_f (u : D.what₂.Word) : ∀ a b, ∑ j, Kf X X.eR a j * X.fR b j = if a = b then 1 else 0 := by
  intro a b
  rw [Kf_apply]
  exact (std X u).2.2.1 a b

theorem hK_e (u : D.what₂.Word) : ∀ c b, ∑ j, Kf X X.fR c j * X.eR b j = if c = b then 1 else 0 := by
  intro c b
  rw [Kf_apply, hE_swap]
  have := (std X u).2.2.1 b c
  change hE _ _ (X.eR b) (X.fR c) = _ at this
  rw [this]
  by_cases h : c = b
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem sum_Kf_mul_zR_eq_zero (u : D.what₂.Word) : ∀ a, ∑ j, Kf X X.eR a j * X.zR u j = 0 := by
  intro a
  rw [Kf_apply]
  exact (std X u).2.2.2.1 a

theorem sigR_inclR (x : X.B.I.E) :
    sigR (AF X.B.I.F) X.B.I.cm.sig (inclR (AF X.B.I.F) x) = inclR (AF X.B.I.F) (X.B.I.cm.sig x) := by
  show (Algebra.TensorProduct.map (AlgHom.id X.B.I.F (AF X.B.I.F)) X.B.I.cm.sig)
      ((1 : AF X.B.I.F) ⊗ₜ[X.B.I.F] x) = (1 : AF X.B.I.F) ⊗ₜ[X.B.I.F] (X.B.I.cm.sig x)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem hR_ratV_left (x : Fin X.B.I.n → X.B.I.E) (y : Fin X.B.I.n → AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    hR (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (AF X.B.I.F) x) y =
      ∑ j, inclR (AF X.B.I.F) (∑ i, star (x i) * X.B.I.J i j) * y j := by
  simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, ratV, sigR_inclR, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem inclR_injective : Function.Injective (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) := by
  intro a b h
  obtain v := (inferInstance : Nonempty (InfinitePlace X.B.I.F)).some
  apply (X.B.I.φ v).injective
  rw [← thetaV_inclR X.B.I v a, ← thetaV_inclR X.B.I v b, h]

theorem sigA_inclE (x : X.B.I.E) :
    Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F) (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.B.I.cm.sig x) := by
  simp [Formalism.UG.sigR, Formalism.UG.inclE]

theorem hA_incl_left (x : Fin X.B.I.n → X.B.I.E) (y : Formalism.L2.SG.HidaSetting.VA X.B.I) :
    hA X.B.I (incl X.B.I x) y =
      ∑ j, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (∑ i, star (x i) * X.B.I.J i j) * y j := by
  simp only [hA, Formalism.UG.hform, Matrix.map_apply, incl, sigA_inclE, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem inclE_injective : Function.Injective (Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F)) :=
  Algebra.TensorProduct.includeLeft_injective (R := X.B.I.F) (S := X.B.I.F)
    (MassDataMassesW.inj_Af X.B.I.F)

end Spec

end MassDataMassesW.NRatW
end
end
