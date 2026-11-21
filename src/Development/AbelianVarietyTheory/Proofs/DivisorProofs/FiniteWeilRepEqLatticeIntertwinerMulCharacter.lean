import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetChar

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

section Alg

variable {R : Type} [CommRing R]

def cut (a : R) (ha : a * a = a) : Rˣ →* Rˣ where
  toFun u := ⟨a * u + (1 - a), a * (u⁻¹ : Rˣ) + (1 - a),
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv,
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv⟩
  map_one' := Units.ext (by simp)
  map_mul' u w := Units.ext (by
    show a * ((u : R) * w) + (1 - a) = (a * u + (1 - a)) * (a * w + (1 - a))
    linear_combination (-((u : R) * w) + u + w - 1) * ha)

theorem cut_val (a : R) (ha : a * a = a) (u : Rˣ) : (cut a ha u : R) = a * u + (1 - a) := rfl

theorem continuous_cut [TopologicalSpace R] [IsTopologicalRing R] (a : R) (ha : a * a = a) :
    Continuous (cut a ha) :=
  Units.continuous_iff.2 ⟨(continuous_const.mul Units.continuous_val).add continuous_const,
    (continuous_const.mul Units.continuous_coe_inv).add continuous_const⟩

theorem mul_det {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, a * (M - 1) i j = 0) :
    a * M.det = a := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R a)
  have hI : ∀ x, x ∈ I ↔ x * a = 0 := fun x => Iff.rfl
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 ((hI _).2 ((mul_comm _ _).trans (h i j)))
  have h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, h1, map_one, det_one, map_one]
  have h3 := (hI _).1 (Ideal.Quotient.eq.1 h2)
  linear_combination h3

end Alg

theorem eq_single {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε = pl D v := by
  obtain ⟨α, rfl, h3, h4⟩ := h
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  rfl

set_option maxHeartbeats 1000000 in

theorem exists_glue (D : D7) (e : HeightOneSpectrum (𝓞 D.host.F) → Formalism.L2.Theta.AE D)
    (hee : ∀ v, e v * e v = e v) (hp : ∀ v, e v * pl D v = e v) :
    ∃ a : Formalism.L2.Theta.AE D, a * a = a ∧ infPart D a = 0 ∧ ∀ v, a * pl D v = e v := by
  obtain ⟨ι, -, -, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h1 : ∀ v (Q : HeightOneSpectrum (𝓞 D.host.E)), Q.under (𝓞 D.host.F) = v →
      ι (finPart D (pl D v)) Q = 1 := fun v Q hQ => by
    refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val Q _ fun n => ?_)
    have := happ (singleV D.host.F v 1) 1 Q n (by
      rw [map_one, hQ, GlobalTheory.PlaceIdem.single_same, sub_self, map_zero]
      exact zero_le)
    rwa [map_one, map_one] at this
  have h0 : ∀ v (Q : HeightOneSpectrum (𝓞 D.host.E)), Q.under (𝓞 D.host.F) ≠ v →
      ι (finPart D (pl D v)) Q = 0 := fun v Q hQ => by
    refine GlobalTheory.PlaceIdem.eq_zero_of_val Q _ fun n => ?_
    have := happ (singleV D.host.F v 1) 0 Q n (by
      rw [map_zero, GlobalTheory.PlaceIdem.single_ne hQ, sub_self, map_zero]
      exact zero_le)
    rwa [map_zero, map_zero, sub_zero] at this
  have hinf : ∀ v, infPart D (pl D v) = 0 := fun v => TensorProduct.zero_tmul _ _
  let f : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.adicCompletion D.host.E :=
    fun Q => ι (finPart D (e (Q.under (𝓞 D.host.F)))) Q
  have hff : ∀ Q, f Q * f Q = f Q := fun Q => by
    simp only [f]
    rw [← GlobalTheory.PlaceIdem.mul_ap, ← map_mul, ← RingHom.map_mul, hee]
  have hint : ∀ Q, f Q ∈ Q.adicCompletionIntegers D.host.E := fun Q => by
    by_cases h : f Q = 0
    · rw [h]; exact zero_mem _
    · rw [mul_left_cancel₀ h ((hff Q).trans (mul_one _).symm)]; exact one_mem _
  let b : FiniteAdeleRing (𝓞 D.host.E) D.host.E := ⟨f, Filter.Eventually.of_forall hint⟩
  have hb : ∀ Q, b Q = f Q := fun _ => rfl
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.PlaceIdem.parts_surj D 0 (ι.symm b)
  have ha3 : ι (finPart D a) = b := by rw [ha2, ι.apply_symm_apply]
  refine ⟨a, GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, ha1, mul_zero]) (ι.injective ?_), ha1,
    fun v => GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ (ι.injective ?_)⟩
  · rw [RingHom.map_mul, map_mul, ha3]
    exact GlobalTheory.PlaceIdem.adele_ext fun Q => hff Q
  · rw [← hp v, RingHom.map_mul, RingHom.map_mul, hinf, mul_zero, mul_zero]
  · rw [← hp v, RingHom.map_mul, RingHom.map_mul, map_mul, map_mul, ha3]
    refine GlobalTheory.PlaceIdem.adele_ext fun Q => ?_
    rw [GlobalTheory.PlaceIdem.mul_ap, GlobalTheory.PlaceIdem.mul_ap]
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · subst hQ; rfl
    · rw [h0 v Q hQ, mul_zero, mul_zero]

theorem exists_select (D : D7) : ∃ a : Formalism.L2.Theta.AE D, a * a = a ∧ infPart D a = 0 ∧
    (∀ v ε, NonSplitAt D v ε → a * algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε = 0) ∧
    ∀ e, IsSplitIdem D e → a * (e + cA D e) = e ∨ a * (e + cA D e) = cA D e := by
  classical
  obtain ⟨a, h1, h2, h3⟩ := exists_glue D (fun v => if h : ∃ e, SplitAt D v e then h.choose else 0)
    (fun v => by
      split_ifs with h
      · exact h.choose_spec.1
      · exact mul_zero _)
    (fun v => by
      split_ifs with h
      · rw [mul_comm]; exact h.choose_spec.pl_mul
      · exact zero_mul _)
  refine ⟨a, h1, h2, fun v ε h => ?_, fun e he => ?_⟩
  · rw [eq_single h.1, h3, dif_neg]
    rintro ⟨e, he⟩
    exact h.2 ⟨e, (isSplitIdem_iff e).2 ⟨v, he⟩, by rw [eq_single h.1, he.2.2]⟩
  · obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 he
    have h : ∃ e, SplitAt D v e := ⟨e, he⟩
    rw [he.2.2, h3, dif_pos h]
    exact (h.choose_spec.unique he).imp Eq.symm Eq.symm

theorem char_norm {D : D7} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n)
    (x y : (Formalism.L2.Theta.AE D)ˣ) (hy : (y : Formalism.L2.Theta.AE D) = x * cA D x) : χ y = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := h
  have := D.host.isCMField_hostE
  have e : y = idF D (Units.map (Algebra.norm (AF D.host.F) : Formalism.L2.Theta.AE D →* AF D.host.F) x) :=
    Units.ext (hy.trans (GlobalTheory.Published.algebraMap_norm_tensor (E := D.host.E) (AF D.host.F)
      (x : Formalism.L2.Theta.AE D)).symm)
  rw [e, h η hη, hη.2.2.1, one_pow]

set_option maxHeartbeats 800000 in

theorem exists_split_character : ∀ (D : D7) (V : HSp D) (χ : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ ν : Formalism.L2.Theta.GA D V →* Circle, Continuous ν ∧ (∀ g ∈ GinfC V, ν g = 1) ∧ (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ∀ x, IsDetAt e V g x → ν g = χ x := by
  intro D V χ n hχ hres
  obtain ⟨a, haa, hinf, hns, hsp⟩ := exists_select D
  haveI : IsTopologicalRing (Formalism.L2.Theta.AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  let d : Formalism.L2.Theta.GA D V →* (Formalism.L2.Theta.AE D)ˣ := Matrix.GeneralLinearGroup.det.comp (matHom V)
  have hd : ∀ g, (d g : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det := fun _ => rfl
  have hc : Continuous d := Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val
  have htriv : ∀ g, (∀ i j, a * (Formalism.L2.Theta.mt V g - 1) i j = 0) → χ (cut a haa (d g)) = 1 := fun g hg => by
    have : cut a haa (d g) = 1 := Units.ext (by
      rw [cut_val, hd, mul_det a _ hg, add_sub_cancel, Units.val_one])
    rw [this, map_one]
  refine ⟨χ.comp ((cut a haa).comp d), hχ.1.comp ((continuous_cut a haa).comp hc), fun g hg => htriv g fun i j => ?_,
    fun v ε h g hg => htriv g fun i j => ?_, fun e he g hg x hx => ?_⟩
  · refine GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]) ?_
    have h1 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g) = 1 := congrArg Units.val hg
    have h2 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g - 1) = 0 := by
      rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
    have h3 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := congrFun (congrFun h2 i) j
    rw [RingHom.map_mul, h3, mul_zero, RingHom.map_zero]
  · rw [← hg i j, ← mul_assoc, hns v ε h, zero_mul]
  · show χ (cut a haa (d g)) = χ x
    have hout := mul_det (1 - (e + cA D e)) (Formalism.L2.Theta.mt V g) fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]
    have hx' : (x : Formalism.L2.Theta.AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
    rcases hsp e he with h | h
    · congr 1
      refine Units.ext ?_
      rw [cut_val, hd, hx']
      linear_combination a * hout + ((Formalism.L2.Theta.mt V g).det - 1) * h
    · have hy : (cut a haa (d g) : Formalism.L2.Theta.AE D) = cA D e * (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
        rw [cut_val, hd]
        linear_combination a * hout + ((Formalism.L2.Theta.mt V g).det - 1) * h
      have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he.1]
      have hu := det_conj_mul V g
      have h1 : (cut a haa (d g) : Formalism.L2.Theta.AE D) * cA D x = 1 := by
        rw [hy, hx', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
        generalize (Formalism.L2.Theta.mt V g).det = z at hu
        linear_combination (z * cA D z - z - cA D z + 1) * hcc + cA D e * hu
      have h2 := char_norm hres x (x * (cut a haa (d g))⁻¹) (by
        rw [Units.val_mul, Units.inv_eq_of_mul_eq_one_right h1])
      rw [map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2.symm

end GlobalTheory.SplitDetChar

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LocalLatStab

open GlobalTheory.AdelicLatMove

variable {D : D7}

def swp (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) →+* EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E : _ →+* _)

theorem map_toEAf (V : HSp D) (g : GA D V) :
    (mt V g).map (toEAf D) = (finMat D.sp.cm.sig V.gram g).map (swp D) := rfl

def swpVec (D : D7) (n : ℕ) (α : Af D.host.F) :
    (Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin n → EAf D) :=
  AddMonoidHom.mk' (fun y i => ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (y i))
    (fun y z => by funext i; simp only [Pi.add_apply, map_add, mul_add])

theorem swpVec_pure {n : ℕ} (α β : Af D.host.F) (x : Fin n → D.host.E) :
    swpVec D n α (fun i => β ⊗ₜ[D.host.F] x i) = fun i => x i ⊗ₜ[D.host.F] (α * β) := by
  funext i
  change ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * (x i ⊗ₜ[D.host.F] β) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mulVec_swpVec (V : HSp D) (g : GA D V) (α : Af D.host.F)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (mt V g).map (toEAf D) *ᵥ swpVec D _ α y = swpVec D _ α (finMat D.sp.cm.sig V.gram g *ᵥ y) := by
  rw [map_toEAf]
  funext i
  change ∑ j, swp D (finMat D.sp.cm.sig V.gram g i j) * (((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (y j)) =
    ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (∑ j, finMat D.sp.cm.sig V.gram g i j * y j)
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_left_comm]

theorem rankOne_mem (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (a : D.host.E) (ha : a ∈ D.host.AA)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    (s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hs : s ∈ latHat D.host.F D.host.E LS)
    (t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E) (ht : t ∈ latHat D.host.F D.host.E LT) :
    rankOne S T a (swpVec D _ 1 s) (swpVec D _ α t) ∈ latO S T LS LT P := by
  change rankOneHom S T a _ _ ∈ _
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨β, hβ, x, hx, rfl⟩ := hs
      obtain ⟨γ, hγ, y, hy, rfl⟩ := ht
      rw [swpVec_pure, swpVec_pure, one_mul]
      apply AddSubgroup.subset_closure
      refine ⟨α * γ * β, (mul_mem (mul_mem hα hγ : α * γ ∈ Formalism.UG.intAd D.host.F) hβ :
        α * γ * β ∈ Formalism.UG.intAd D.host.F), fun v hv => ?_, a, ha, x, hx, y, hy,
        rankOne_pure S T a x y β (α * γ)⟩
      rw [map_mul, map_mul, hP v hv, zero_mul, zero_mul]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add, map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg, map_neg]; exact neg_mem hy
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg, map_neg]; exact neg_mem hy

theorem actO_mem (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : GA D S) (h : GA D T)
    (hg : ∀ y ∈ latHat D.host.F D.host.E LS, finMat D.sp.cm.sig S.gram g *ᵥ y ∈ latHat D.host.F D.host.E LS)
    (hh : ∀ y ∈ latHat D.host.F D.host.E LT, finMat D.sp.cm.sig T.gram h *ᵥ y ∈ latHat D.host.F D.host.E LT)
    (u : WO S T) (hu : u ∈ latO S T LS LT P) : actO S T g h u ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := (one_mem _ : (1 : Af D.host.F) ∈ Formalism.UG.intAd D.host.F)
    have e := rankOne_pure S T a s t (1 * 1) (α * 1)
    rw [← swpVec_pure, ← swpVec_pure, mul_one, mul_one, mul_one] at e
    rw [← e, actO_rankOne, mulVec_swpVec, mulVec_swpVec]
    exact rankOne_mem S T LS LT P a ha α hα hP _
      (hg _ (AddSubgroup.subset_closure ⟨1, h1, s, hs, rfl⟩)) _
      (hh _ (AddSubgroup.subset_closure ⟨1, h1, t, ht, rfl⟩))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem finMat_mul_inv (V : HSp D) (g : GA D V) :
    finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g⁻¹ = 1 := by
  let f := Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
  change (mt V g).map f * (mt V g⁻¹).map f = 1
  rw [← Matrix.map_mul (f := f), ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inv_keeps (V : HSp D) (L : Set (Fin V.rank → D.host.E)) (g : GA D V)
    (hg : ∀ y, y ∈ latHat D.host.F D.host.E L ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E L) :
    ∀ y ∈ latHat D.host.F D.host.E L, finMat D.sp.cm.sig V.gram g⁻¹ *ᵥ y ∈ latHat D.host.F D.host.E L := by
  intro y hy
  rw [hg, Matrix.mulVec_mulVec, finMat_mul_inv, Matrix.one_mulVec]
  exact hy

theorem mem_latO_place_iff_actO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, IsPlaceIdem D v ε → ∀ (g : GA D S) (h : GA D T), (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔ (finMat D.sp.cm.sig S.gram g).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) → (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔ (finMat D.sp.cm.sig T.gram h).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) → ∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v) := by
  intro D S T ΛS ΛT _ _ v _ _ g h hg hh u
  refine ⟨actO_mem S T _ _ _ g h (fun y hy => (hg y).1 hy) (fun y hy => (hh y).1 hy) u, fun hu => ?_⟩
  have h1 := actO_mem S T _ _ _ g⁻¹ h⁻¹ (inv_keeps S _ g hg) (inv_keeps T _ h hh) _ hu
  have h2 := actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at h2
  rwa [h2] at h1

end GlobalTheory.LocalLatStab

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_localHomLattice_of_keeps_completedLattices : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, IsPlaceIdem D v ε → ∀ (g : GA D S) (h : GA D T), (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔ (finMat D.sp.cm.sig S.gram g).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) → (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔ (finMat D.sp.cm.sig T.gram h).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) → ∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v) := by
  first | exact @GlobalTheory.LocalLatStab.mem_latO_place_iff_actO | exact GlobalTheory.LocalLatStab.mem_latO_place_iff_actO | (intros; apply GlobalTheory.LocalLatStab.mem_latO_place_iff_actO <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicCharacter_trivial_of_local : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ g ∈ GinfC V, ν g = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.LocalGlobalChar.eq_one_of_local | exact GlobalTheory.LocalGlobalChar.eq_one_of_local | (intros; apply GlobalTheory.LocalGlobalChar.eq_one_of_local <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unitary_character_trivial_at_nonsplit_place : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ v ε, NonSplitAt D v ε → ∀ ν : GA D V →* Circle, (∀ k, SuppPl ε V k → (∀ y, y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))) → ν k = 1) → ∀ g, SuppPl ε V g → ν g = 1 := by
  first | exact @GlobalTheory.InertChar.char_eq_one_of_nonSplit | exact GlobalTheory.InertChar.char_eq_one_of_nonSplit | (intros; apply GlobalTheory.InertChar.char_eq_one_of_nonSplit <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinWeilForm

open GlobalTheory.SplitDetChar GlobalTheory.SplitScalar

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {χS χT : (AE D)ˣ →* Circle}

theorem placeIdem_smul_self {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T}
    (hu : u ∈ latO S T ΛS ΛT fun w => w = v) : algebraMap (AF D.host.F) (AE D) ε • u = u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = α := GlobalTheory.SplitIdem.af_ext _ fun w => by
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hP w hw, mul_zero]
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (mul_zero _) hβα
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h']
  | neg x _ h => rw [smul_neg, h]

set_option maxHeartbeats 800000 in

theorem exists_half_character {a : AE D} (ha : IsHalfIdem D a) (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ)
    (hχ : IsHeckeChar D χ) (hres : ResEta D χ n) :
    ∃ ν : GA D V →* Circle, Continuous ν ∧ (∀ g ∈ GinfC V, ν g = 1) ∧
      (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) ∧
      (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ∀ x, IsDetAt e V g x → ν g = χ x) ∧
      ∀ g (x : (AE D)ˣ), (x : AE D) = a * (Formalism.L2.Theta.mt V g).det + (1 - a) → ν g = χ x := by
  obtain ⟨haa, -, hinf, hsp', hns⟩ := ha
  have hsp : ∀ e, IsSplitIdem D e → a * (e + cA D e) = e ∨ a * (e + cA D e) = cA D e := fun e he =>
    (hsp' e he).imp (fun h => by rw [mul_add, h.1, h.2, add_zero]) fun h => by rw [mul_add, h.1, h.2, zero_add]
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  let d : GA D V →* (AE D)ˣ := Matrix.GeneralLinearGroup.det.comp (matHom V)
  have hd : ∀ g, (d g : AE D) = (Formalism.L2.Theta.mt V g).det := fun _ => rfl
  have hc : Continuous d := Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val
  have htriv : ∀ g, (∀ i j, a * (Formalism.L2.Theta.mt V g - 1) i j = 0) → χ (cut a haa (d g)) = 1 := fun g hg => by
    have : cut a haa (d g) = 1 := Units.ext (by
      rw [cut_val, hd, mul_det a _ hg, add_sub_cancel, Units.val_one])
    rw [this, map_one]
  refine ⟨χ.comp ((cut a haa).comp d), hχ.1.comp ((continuous_cut a haa).comp hc), fun g hg => htriv g fun i j => ?_,
    fun v ε h g hg => htriv g fun i j => ?_, fun e he g hg x hx => ?_,
    fun g x hx => congrArg χ (Units.ext hx.symm)⟩
  · refine GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]) ?_
    have h1 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g) = 1 := congrArg Units.val hg
    have h2 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g - 1) = 0 := by
      rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
    have h3 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := congrFun (congrFun h2 i) j
    rw [RingHom.map_mul, h3, mul_zero, RingHom.map_zero]
  · rw [← hg i j, ← mul_assoc, mul_comm a, hns v ε h, zero_mul]
  · show χ (cut a haa (d g)) = χ x
    have hout := mul_det (1 - (e + cA D e)) (Formalism.L2.Theta.mt V g) fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]
    have hx' : (x : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := hx
    rcases hsp e he with h | h
    · congr 1
      refine Units.ext ?_
      rw [cut_val, hd, hx']
      linear_combination a * hout + ((Formalism.L2.Theta.mt V g).det - 1) * h
    · have hy : (cut a haa (d g) : AE D) = cA D e * (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
        rw [cut_val, hd]
        linear_combination a * hout + ((Formalism.L2.Theta.mt V g).det - 1) * h
      have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he.1]
      have hu := det_conj_mul V g
      have h1 : (cut a haa (d g) : AE D) * cA D x = 1 := by
        rw [hy, hx', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
        generalize (Formalism.L2.Theta.mt V g).det = z at hu
        linear_combination (z * cA D z - z - cA D z + 1) * hcc + cA D e * hu
      have h2 := char_norm hres x (x * (cut a haa (d g))⁻¹) (by
        rw [Units.val_mul, Units.inv_eq_of_mul_eq_one_right h1])
      rw [map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2.symm

theorem exists_theta (hψ : IsStdChar D ψ (-1)) (S T : HSp D) : ∃ f, f ≠ 0 ∧ IsThetaFunO ψ S T f := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hcs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hcs S) (hcs T) _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
  obtain ⟨hth, -⟩ := hf 1
  simp only [one_mul] at hth
  exact ⟨f, f0, hth⟩

theorem exists_vacuum (hψ : IsStdChar D ψ (-1)) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)} (h : IsLatRep hψ.1 ΛS ΛT w lam Om) :
    ∃ f, f ≠ 0 ∧ IsThetaFunO ψ S T f ∧ ∀ v η, NonSplitAt D v η →
      ∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f := by
  obtain ⟨f, f0, hf⟩ := exists_theta hψ S T
  obtain ⟨e, he, e0⟩ : ∃ e, Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) e ∧ e ≠ 0 := by
    by_contra hn
    push_neg at hn
    have : (⊤ : Submodule ℂ (thetaSub ψ S T)) ≤ ⊥ := by
      rw [← h.span, Submodule.span_le]
      rintro _ ⟨x, e, he, rfl⟩
      rw [hn e he, map_zero]
      exact zero_mem _
    exact f0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 (this (Submodule.mem_top (x := ⟨f, hf⟩)))))
  refine ⟨e, fun h0 => e0 (Subtype.ext h0), e.2, fun v η hv u hu => ?_⟩
  obtain ⟨b, hb, hb'⟩ := exists_half_of_nonSplit hv
  have hu' := GlobalTheory.PlaceModel.latO_le_top _ hu
  let a : XF S T := XF.mk u (latO_fin hu')
  have ha : a ∈ latF S T ΛS ΛT := hu'
  have e0 : algebraMap (AF D.host.F) (AE D) η • u = u := placeIdem_smul_self hv.1 hu
  have e1 : a = 2 • (b • a) := by
    rw [two_nsmul, ← add_smul, ← two_mul, hb']
    exact XF.ext e0.symm
  have e2 : b • a ∈ latF S T ΛS ΛT := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b hb _ ha
  have h1 := congrArg Subtype.val (he a ha)
  rw [coe_opF] at h1
  have h2 : phase ψ w a = 1 := by rw [e1]; exact phase_two h.sd w e2
  rwa [h2, one_smul] at h1

theorem actO_actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  rw [actO, actO, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv,
    Matrix.mul_one]

theorem exists_scalar (hψ : IsStdChar D ψ (-1)) {o₁ o₂ : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (h₁ : IsFinWeil ψ S T ΛS ΛT χS χT o₁) (h₂ : IsFinWeil ψ S T ΛS ΛT χS χT o₂) (p : GA D S × GA D T) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → o₁ p f = c • o₂ p f := by
  obtain ⟨a, ha, k, hk, e1⟩ := (GlobalTheory.UnitarySplit.real_finite_split D S).1 p.1
  obtain ⟨a', ha', k', hk', e2⟩ := (GlobalTheory.UnitarySplit.real_finite_split D T).1 p.2
  have e : p = (a, a') * (k, k') := Prod.ext e1 e2
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ S T (o₁ (k, k') * o₂ (k⁻¹, k'⁻¹))
    (fun f hf => h₁.pres _ _ (h₂.pres _ _ hf))
    (fun u f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, h₂.Heisenberg₂ _ (inv_mem hk) _ (inv_mem hk') u f hf,
        h₁.Heisenberg₂ _ hk _ hk' _ _ (h₂.pres _ _ hf), actO_actO_inv])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, h₁.unit μ 𝓕 hμ h𝓕 _ _ (h₂.pres _ _ hf), h₂.unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨c, hc, fun f hf => ?_⟩
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₁.triv _ ha _ ha' _ (h₁.pres _ _ hf),
    h₂.triv _ ha _ ha' _ (h₂.pres _ _ hf), ← h _ (h₂.pres _ _ hf), Module.End.mul_apply, ← Module.End.mul_apply (o₂ _),
    ← map_mul, show ((k⁻¹, k'⁻¹) * (k, k') : GA D S × GA D T) = 1 from inv_mul_cancel (k, k'), map_one, Module.End.one_apply]

theorem exists_character (hψ : IsStdChar D ψ (-1)) {o₁ o₂ : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (h₁ : IsFinWeil ψ S T ΛS ΛT χS χT o₁) (h₂ : IsFinWeil ψ S T ΛS ΛT χS χT o₂) :
    ∃ ν : GA D S × GA D T →* Circle, Continuous ν ∧ ∀ p f, IsThetaFunO ψ S T f → o₁ p f = (ν p : ℂ) • o₂ p f := by
  choose c hc h using exists_scalar hψ h₁ h₂
  obtain ⟨f, f0, hf⟩ := exists_theta hψ S T
  have hne : ∀ p, o₂ p f ≠ 0 := fun p h0 => f0 (by
    have := congrArg (o₂ p⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this)
  refine ⟨MonoidHom.mk' (fun p => ⟨c p, mem_sphere_zero_iff_norm.2 (hc p)⟩) fun p q => Circle.ext ?_, ?_, h⟩
  · show c (p * q) = c p * c q
    refine smul_left_injective ℂ (hne (p * q)) ?_
    show c (p * q) • o₂ (p * q) f = (c p * c q) • o₂ (p * q) f
    rw [← h _ f hf, map_mul, Module.End.mul_apply, h p _ (h₁.pres _ _ hf), h q f hf, map_smul, smul_smul, map_mul,
      Module.End.mul_apply]
  · refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun q => ?_) _
    obtain ⟨u, hu⟩ := Function.ne_iff.1 (hne q)
    refine (((h₁.cont f hf u).continuousAt).div (h₂.cont f hf u).continuousAt hu).congr ?_
    filter_upwards [(h₂.cont f hf u).continuousAt.eventually_ne hu] with p hp
    show o₁ p f u / o₂ p f u = c p
    rw [h p f hf, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hp]

theorem finMat_one (V : HSp D) : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 :=
  congrArg Units.val (finHom V).map_one

theorem exists_isDetAt {e : AE D} (he : IsSplitIdem D e) (V : HSp D) (g : GA D V) : ∃ x, IsDetAt e V g x :=
  ⟨cut e he.1 (Matrix.GeneralLinearGroup.det (matHom V g)), rfl⟩

theorem unique (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {o₁ o₂ : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (h₁ : IsFinWeil ψ S T ΛS ΛT χS χT o₁) (h₂ : IsFinWeil ψ S T ΛS ΛT χS χT o₂) (p : GA D S × GA D T)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) : o₁ p f = o₂ p f := by
  obtain ⟨ν, hc, hν⟩ := exists_character hψ h₁ h₂
  obtain ⟨lam, hlam, -⟩ := exists_goodNorm D
  obtain ⟨w, Om, hOm⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨f₀, f0, hf₀, hvac⟩ := exists_vacuum hψ hOm
  have key : ∀ q, o₁ q f₀ = f₀ → o₂ q f₀ = f₀ → ν q = 1 := fun q a b => by
    have := hν q f₀ hf₀
    rw [a, b] at this
    exact Circle.ext (smul_left_injective ℂ f0 (this.symm.trans (one_smul ℂ f₀).symm))
  have hreal : ∀ g ∈ GinfC S, ∀ k ∈ GinfC T, ν (g, k) = 1 := fun g hg k hk =>
    key _ (h₁.triv g hg k hk _ hf₀) (h₂.triv g hg k hk _ hf₀)
  have hsplit : ∀ e, IsSplitIdem D e → ∀ g k, SuppAt e S g → SuppAt e T k → ν (g, k) = 1 := fun e he g k hg hk => by
    obtain ⟨x, hx⟩ := exists_isDetAt he S g
    obtain ⟨y, hy⟩ := exists_isDetAt he T k
    obtain ⟨r, hr, a⟩ := h₁.split e he g k hg hk x y hx hy
    obtain ⟨r', hr', b⟩ := h₂.split e he g k hg hk x y hx hy
    obtain ⟨ℓ, hℓ, f₁, hf₁, h0⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ hψ S T e he
    have c := a ℓ hℓ f₁ hf₁
    rw [hν _ _ hf₁, map_smul, b ℓ hℓ f₁ hf₁, smul_eq_mul, ← mul_assoc, ← mul_assoc] at c
    have c2 := mul_right_cancel₀ (Circle.coe_ne_zero _) (mul_right_cancel₀ h0 c)
    have c3 := congrArg norm c2
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hr'.le] at c3
    rw [c3] at c2
    exact Circle.ext (mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne') (c2.trans (one_mul _).symm))
  have hin : ∀ v η, NonSplitAt D v η → ∀ g k, SuppPl η S g → SuppPl η T k →
      (∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g k u ∈ (latO S T ΛS ΛT fun w => w = v)) →
      ν (g, k) = 1 := fun v η hv g k hg hk hst =>
    key _ (h₁.inert v η hv g k hg hk hst _ hf₀ (hvac v η hv)) (h₂.inert v η hv g k hg hk hst _ hf₀ (hvac v η hv))
  have s1 : ∀ (V : HSp D) (a : AE D) i j,
      a * (Formalism.L2.Theta.mt V 1 - 1) i j = (Formalism.L2.Theta.mt V 1 - 1) i j := fun V a i j => by
    rw [mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have hl := GlobalTheory.T.unitaryAdelicCharacter_trivial_of_local D S (ν.comp (MonoidHom.inl _ _)) (hc.comp (Continuous.prodMk_left 1))
    (fun g hg => hreal g hg 1 (one_mem _)) (fun e he g hg => hsplit e he g 1 hg (s1 T _))
    fun v η hv => GlobalTheory.T.adelic_unitary_character_trivial_at_nonsplit_place D S ΛS hS v η hv _ fun g hg hst => hin v η hv g 1 hg (s1 T _)
      (GlobalTheory.T.mem_localHomLattice_of_keeps_completedLattices D S T ΛS ΛT hS hT v η hv.1 g 1 hst fun y => by rw [finMat_one, Matrix.one_mulVec])
  have hr := GlobalTheory.T.unitaryAdelicCharacter_trivial_of_local D T (ν.comp (MonoidHom.inr _ _)) (hc.comp (Continuous.prodMk_right 1))
    (fun g hg => hreal 1 (one_mem _) g hg) (fun e he g hg => hsplit e he 1 g (s1 S _) hg)
    fun v η hv => GlobalTheory.T.adelic_unitary_character_trivial_at_nonsplit_place D T ΛT hT v η hv _ fun g hg hst => hin v η hv 1 g (s1 S _) hg
      (GlobalTheory.T.mem_localHomLattice_of_keeps_completedLattices D S T ΛS ΛT hS hT v η hv.1 1 g (fun y => by rw [finMat_one, Matrix.one_mulVec]) hst)
  have h1 : ν p = 1 := by
    have : p = (p.1, 1) * (1, p.2) := Prod.ext (mul_one _).symm (one_mul _).symm
    rw [this, map_mul, show ν (p.1, 1) = 1 from hl p.1, show ν (1, p.2) = 1 from hr p.2, mul_one]
  rw [hν p f hf, h1, Circle.coe_one, one_smul]

theorem finWeil_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (χS χT : (AE D)ˣ →* Circle) (nS nT : ℕ), IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS nS → ResEta D χT nT → ∀ of : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsFinWeil ψ S T ΛS ΛT χS χT of → ∀ (lam : ℕ →* ℂ), GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)), IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε, IsHalfIdem D ε → ∀ (g : GA D S) (h : GA D T) (x y : (AE D)ˣ), (x : AE D) = ε * (Formalism.L2.Theta.mt S g).det + (1 - ε) → (y : AE D) = ε * (Formalism.L2.Theta.mt T h).det + (1 - ε) → ∀ f : thetaSub ψ S T, of (g, h) f = ((((χT x)⁻¹ * χS y : Circle) : ℂ)) • (Om (g, h) f : WO S T → ℂ) := by
  intro D ψ hψ S T ΛS ΛT hS hT χS χT nS nT hχS hχT hrS hrT of hof lam hlam hsq w Om h ε hε g₀ k₀ x₀ y₀ hx₀ hy₀ f₀
  obtain ⟨c, c1, c2, c3, c4, c5⟩ := exists_half_character hε S χT _ hχT hrT
  obtain ⟨d, d1, d2, d3, d4, d5⟩ := exists_half_character hε T χS _ hχS hrS
  let z : GA D S × GA D T → Circle := fun p => (c p.1)⁻¹ * d p.2
  have z1 : z 1 = 1 := by simp [z]
  have z2 : ∀ p q, z (p * q) = z p * z q := fun p q => by
    simp only [z, Prod.fst_mul, Prod.snd_mul, map_mul, _root_.mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have z3 : Continuous z := (c1.comp continuous_fst).inv.mul (d1.comp continuous_snd)
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T)
    ({ toFun := fun p => (z p : ℂ) • Om p
       map_one' := by rw [z1, Circle.coe_one, one_smul, map_one]
       map_mul' := fun p q => by rw [z2, map_mul, Circle.coe_mul, smul_mul_smul_comm] } :
      GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T))
  have ho : ∀ p f (hf : IsThetaFunO ψ S T f), om p f = (z p : ℂ) • (Om p ⟨f, hf⟩ : WO S T → ℂ) :=
    fun p f hf => hom p ⟨f, hf⟩
  have hom' : IsFinWeil ψ S T ΛS ΛT χS χT om := by
    refine ⟨⟨fun p f hf => ?_, fun f hf u => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
      fun g hg k hk u f hf => ?_, fun e he g k hg hk x y hx hy => ?_, fun v η hv g k hg hk hst f hf hfix => ?_⟩
    · rw [ho p f hf]
      exact (thetaSub ψ S T).smul_mem _ (Om p ⟨f, hf⟩).2
    · simp only [ho _ f hf, Pi.smul_apply, smul_eq_mul]
      exact (continuous_subtype_val.comp z3).mul (h.cont hS hT ⟨f, hf⟩ u)
    · rw [← h.unit hlam μ 𝓕 hμ h𝓕 p ⟨f, hf⟩, ho p f hf]
      refine lintegral_congr fun u => ?_
      rw [Pi.smul_apply, enorm_smul, ← ofReal_norm_eq_enorm (z p : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]
    · rw [ho _ f hf, h.real_triv hg hk, show z (g, k) = 1 by simp [z, c2 g hg, d2 k hk], Circle.coe_one, one_smul]
    · obtain ⟨f', h1, h2⟩ := h.Heisenberg₂ hψ hg hk u ⟨f, hf⟩
      rw [ho _ f hf, heisO_smul, ← h2, ← h1]
      exact hom _ f'
    · obtain ⟨r, hr, h1⟩ := h.split hsq he hg hk
      refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
      rw [ho _ f hf, map_smul, h1 ℓ hℓ, smul_eq_mul,
        show z (g, k) = splitFacO χS χT x y by simp only [z, splitFacO, c4 e he g hg x hx, d4 e he k hk y hy]]
      ring
    · rw [ho _ f hf, h.inert hv hg hk (fun u hu => (hst u).1 hu) ⟨f, hf⟩ hfix,
        show z (g, k) = 1 by simp [z, c3 v η hv g hg, d3 v η hv k hk], Circle.coe_one, one_smul]
  rw [unique hψ hS hT hof hom' _ _ f₀.2, ho _ _ f₀.2, ← c5 g₀ x₀ hx₀, ← d5 k₀ y₀ hy₀]

end GlobalTheory.FinWeilForm

end
end
