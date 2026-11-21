import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ColPhaseCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section LeviMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem resT_of_mem (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E) :
    resT TR v z = TR.res v ⟨z, hz⟩ := by
  unfold resT; rw [dif_pos hz]

theorem res_eq_zero_of_Z (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E)
    (hZ : ZMod' X.B.I X.B.g z) : TR.res v ⟨z, hz⟩ = 0 :=
  (TR.res_ker ⟨z, hz⟩).2 (Z_smul X.B.I X.B.g X.ew_int hZ) v

def PhiSub (x : X.B.I.Gf) (i : Fin D.R.k) : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {z | ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
    ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z)}
  add_mem' {z w} hz hw := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w) =
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) +
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w) := by
      simp only [Matrix.mulVec_add, hA_add_right, mul_add, Finset.sum_add_distrib]; ring
    rw [e]; exact Z_add X.B.I X.B.g hz hw
  zero_mem' := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ 0) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) 0)
    have h0 : ∀ u : VA X.B.I, hA X.B.I u 0 = 0 := fun u => (hL X.B.I u).map_zero
    simp only [Matrix.mulVec_zero, h0, mul_zero, Finset.sum_const_zero, sub_zero]
    exact Z_zero X.B.I X.B.g
  smul_mem' c z hz := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) := by
      simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]; exact Z_smul X.B.I X.B.g c.2 hz

theorem dual_beta_reference_congruence (i : Fin D.R.k) (a : Fin D.R.rS) : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.e0 a)) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 a).2.2.1

theorem leviM_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset)
    (hyb : ∀ j, X.B.I.fmat y *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw))
    (hxe : ∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v := by
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1

  have key : ∀ i, Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) ≤ PhiSub x i := by
    intro i
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro z (⟨a, rfl⟩ | ⟨m, rfl⟩)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.e0 a) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.e0 a))
        refine Z_sub X.B.I X.B.g ?_ (Z_sum X.B.I X.B.g _ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (dual_beta_reference_congruence l a))
        have hQ : Mo X.B.I X.B.g (Set.range X.e0) ≤ Qs X.B.I X.B.g (X.bwd i) :=
          sup_le (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact dual_beta_reference_congruence i b)) (mL_Qs X.B.I X.B.g (hbwd i))
        exact hQ (hxe a)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m))
        have hw : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) = X.ew * hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) := by
          conv_lhs => rw [X.bw_w m, Matrix.mulVec_smul, hA_smul_right]
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m) =
            (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) *
              (hA X.B.I (X.bwd l) (X.bw m) - if l = m then X.ew else 0) := by
          simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          ring
        have e2 : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew = 0 := by
          rw [hw]
          have := X.ew_idem
          linear_combination (-(hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m))) * this
        rw [e, e2, zero_sub]
        have := Z_sum X.B.I X.B.g Finset.univ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (X.bw_dual l m)
        obtain ⟨t, ht, htt⟩ := this
        exact ⟨-t, neg_mem ht, by rw [htt]; ring⟩
    · rintro _ ⟨w, hw, rfl⟩
      show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w))
      refine ⟨hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w, ?_, ?_⟩
      · exact sub_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx hw)) (sum_mem fun l _ =>
          mul_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (hA_int X.B.I (hbwd l) hw))
      · simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
  ext i j
  have hxy : X.B.I.fmat (x * y) *ᵥ X.bw j = X.B.I.fmat x *ᵥ (X.B.I.fmat y *ᵥ X.bw j) := by
    rw [fmat_mul, Matrix.mulVec_mulVec]
  have hZ := key i (hyb j)
  simp only [PhiSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hZ
  rw [← hxy] at hZ

  have hI1 : hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    hA_int X.B.I (hbwd i) (K_mv X.B.I (K_mul X.B.I hx hy) (hbw j))
  have hI2 : ∀ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))
  have hI3 : ∀ l, hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd l) (K_mv X.B.I hy (hbw j))
  have hIs : ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈
      IntAf X.B.I.F X.B.I.E := sum_mem fun l _ => mul_mem (hI2 l) (hI3 l)
  have hD := res_eq_zero_of_Z TR v (sub_mem hI1 hIs) hZ
  simp only [leviM, Matrix.mul_apply]
  rw [resT_of_mem TR v hI1]
  simp only [resT_of_mem TR v (hI2 _), resT_of_mem TR v (hI3 _)]
  have e3 : (⟨hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j), hI1⟩ : IntAf X.B.I.F X.B.I.E) =
      ⟨_, sub_mem hI1 hIs⟩ + ∑ l, (⟨_, hI2 l⟩ : IntAf X.B.I.F X.B.I.E) * ⟨_, hI3 l⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
    ring
  rw [e3, map_add, hD, zero_add, map_sum]
  simp only [map_mul]

end LeviMul

end Formalism.L2.SG.NormCut
end
end

section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence Matrix

namespace Formalism.L2.SG.NormCut

section Dual

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def repr0 (v : VA X.B.I) : VA X.B.I :=
  (∑ a, hA X.B.I (X.f0 a) v • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) v • X.f0 a) - hA X.B.I X.z0 v • X.z0 +
    (∑ l, hA X.B.I (X.bwd l) v • X.bw l) + (∑ l, hA X.B.I (X.bw l) v • X.bwd l)

theorem Z_smul_mL {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {u : VA X.B.I} (hc : ZMod' X.B.I X.B.g c)
    (hu : u ∈ X.B.I.Lf) : c • u ∈ mL X.B.I X.B.g := by
  obtain ⟨t, ht, rfl⟩ := hc
  unfold mL
  refine Submodule.subset_span ⟨(⟨t, ht⟩ : IntAf X.B.I.F X.B.I.E) • u, Submodule.smul_mem _ _ hu, ?_⟩
  rw [mul_smul]
  rfl

theorem reference_repr_add (v w : VA X.B.I) : repr0 X (v + w) = repr0 X v + repr0 X w := by
  have hadd : ∀ x, hA X.B.I x (v + w) = hA X.B.I x v + hA X.B.I x w := fun x => by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [repr0, hadd, add_smul, Finset.sum_add_distrib]
  abel

theorem reference_repr_smul (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (v : VA X.B.I) : repr0 X (c • v) = c • repr0 X v := by
  have hsm : ∀ x, hA X.B.I x (c • v) = c * hA X.B.I x v := fun x => by
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [repr0, hsm, mul_smul, smul_add, smul_sub, Finset.smul_sum]

theorem frame_Lf : (∀ a, X.e0 a ∈ X.B.I.Lf) ∧ (∀ a, X.f0 a ∈ X.B.I.Lf) ∧ X.z0 ∈ X.B.I.Lf ∧
    (∀ l, X.bw l ∈ X.B.I.Lf) ∧ (∀ l, X.bwd l ∈ X.B.I.Lf) := by
  exact ⟨fun a => (X.vectorsInLattice.1 a).1, fun a => (X.vectorsInLattice.1 a).2, X.vectorsInLattice.2.1, fun l => (X.vectorsInLattice.2.2 l).1,
    fun l => (X.vectorsInLattice.2.2 l).2⟩

theorem reference_repr_mem_lattice {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : repr0 X v ∈ X.B.I.Lf := by
  have hincl : ∀ e : X.B.I.E, sigA X.B.I (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) e) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (star e) := by
    intro e
    first
      | rfl
      | simp [sigA, Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]
  have hInt : ∀ s ∈ IntAf X.B.I.F X.B.I.E, sigA X.B.I s ∈ IntAf X.B.I.F X.B.I.E := by
    have hle : IntAf X.B.I.F X.B.I.E ≤ (IntAf X.B.I.F X.B.I.E).comap (sigA X.B.I) := by
      show Subring.closure _ ≤ _
      rw [Subring.closure_le]
      rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inl ⟨⟨_, RingOfIntegers.mapRingEquiv (starRingAut : RingAut X.B.I.E) a, rfl⟩, ?_⟩)
        first
          | rfl
          | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
        simp [sigA, Formalism.UG.sigR]
    exact fun s hs => hle hs
  have hzl : ∀ v : VA X.B.I, hA X.B.I 0 v = 0 := fun v => by simp [hA, Formalism.UG.hform]
  have hzr : ∀ x : VA X.B.I, hA X.B.I x 0 = 0 := fun x => by simp [hA, Formalism.UG.hform]
  have hal : ∀ x x' v : VA X.B.I, hA X.B.I (x + x') v = hA X.B.I x v + hA X.B.I x' v := fun x x' v => by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have har : ∀ x v v' : VA X.B.I, hA X.B.I x (v + v') = hA X.B.I x v + hA X.B.I x v' := fun x v v' => by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hsl : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I (s • x) y = sigA X.B.I s * hA X.B.I x y := by
    intro s x y
    simp only [hA, sigA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsr : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I x (s • y) = s * hA X.B.I x y := by
    intro s x y
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsl' : ∀ (r : IntAf X.B.I.F X.B.I.E) (x y : VA X.B.I),
      hA X.B.I (r • x) y = sigA X.B.I r * hA X.B.I x y := fun r x y => hsl r x y
  have hsr' : ∀ (r : IntAf X.B.I.F X.B.I.E) (x y : VA X.B.I),
      hA X.B.I x (r • y) = r * hA X.B.I x y := fun r x y => hsr r x y
  have hgen : ∀ y ∈ X.B.I.L, ∀ y' ∈ X.B.I.L,
      hA X.B.I (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y i))
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y' i)) ∈ IntAf X.B.I.F X.B.I.E := by
    intro y hy y' hy'
    obtain ⟨b, hb⟩ := (X.B.I.L_dual y').1 hy' y hy
    have e : hA X.B.I (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y i))
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y' i)) =
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.UG.hform (starRingEnd _) X.B.I.J y y') := by
      simp only [hA, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, hincl, starRingEnd_apply]
    rw [e, ← hb]
    show _ ∈ Subring.closure _
    exact Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)
  have hpair : ∀ x ∈ X.B.I.Lf, ∀ w ∈ X.B.I.Lf, hA X.B.I x w ∈ IntAf X.B.I.F X.B.I.E := by
    intro x hx w hw
    unfold AutInst.Lf lamAf at hx hw
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hz
      induction hw using Submodule.span_induction with
      | mem z' hz' =>
        obtain ⟨⟨y', hy'⟩, rfl⟩ := hz'
        exact hgen y hy y' hy'
      | zero => rw [hzr]; exact zero_mem _
      | add a b _ _ ha hb => rw [har]; exact add_mem ha hb
      | smul r a _ ha => rw [hsr']; exact mul_mem r.2 ha
    | zero => rw [hzl]; exact zero_mem _
    | add a b _ _ ha hb => rw [hal]; exact add_mem ha hb
    | smul r a _ ha => rw [hsl']; exact mul_mem (hInt _ r.2) ha
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  have hterm : ∀ x ∈ X.B.I.Lf, ∀ u ∈ X.B.I.Lf, hA X.B.I x v • u ∈ X.B.I.Lf := fun x hx u hu =>
    Submodule.smul_mem _ (⟨_, hpair x hx v hv⟩ : IntAf X.B.I.F X.B.I.E) hu
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) (hterm _ hz _ hz)) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => hterm _ (hf a) _ (he a)
  · exact Submodule.sum_mem _ fun a _ => hterm _ (he a) _ (hf a)
  · exact Submodule.sum_mem _ fun l _ => hterm _ (hbd l) _ (hb l)
  · exact Submodule.sum_mem _ fun l _ => hterm _ (hb l) _ (hbd l)

def ReprSub : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {v | v - repr0 X v ∈ mL X.B.I X.B.g}
  add_mem' {v w} hv hw := by
    show v + w - repr0 X (v + w) ∈ mL X.B.I X.B.g
    rw [reference_repr_add, show v + w - (repr0 X v + repr0 X w) = (v - repr0 X v) + (w - repr0 X w) by abel]
    exact add_mem hv hw
  zero_mem' := by
    show (0 : VA X.B.I) - repr0 X 0 ∈ mL X.B.I X.B.g
    have : repr0 X 0 = 0 := by simpa using reference_repr_smul X 0 0
    rw [this, sub_zero]; exact zero_mem _
  smul_mem' c v hv := by
    show (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v - repr0 X ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) ∈ mL X.B.I X.B.g
    rw [reference_repr_smul, ← smul_sub]
    exact Submodule.smul_mem _ c hv

theorem T_gen (s : VA X.B.I) (tA tB : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (tC : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (tP tQ : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hs : s = (∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l))
    (h1 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) s - tA a))
    (h2 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) s - tB a))
    (h3 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 s - tC))
    (h4 : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd l) s - tP l))
    (h5 : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) s - tQ l)) :
    s ∈ ReprSub X := by
  have hneg' : ∀ x y, ZMod' X.B.I X.B.g (x - y) → ZMod' X.B.I X.B.g (y - x) := by
    rintro x y ⟨t, ht, e⟩
    exact ⟨-t, neg_mem ht, by rw [mul_neg, ← e, neg_sub]⟩
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  show s - repr0 X s ∈ mL X.B.I X.B.g
  have h0 : s - repr0 X s = ((∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l)) - repr0 X s := congrArg (· - repr0 X s) hs
  rw [h0]
  have hexp : ((∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l)) - repr0 X s =
      (∑ a, (tA a - hA X.B.I (X.f0 a) s) • X.e0 a) + (∑ a, (tB a - hA X.B.I (X.e0 a) s) • X.f0 a) -
        (tC - hA X.B.I X.z0 s) • X.z0 + (∑ l, (tP l - hA X.B.I (X.bwd l) s) • X.bw l) +
        (∑ l, (tQ l - hA X.B.I (X.bw l) s) • X.bwd l) := by
    unfold repr0
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hexp]
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) (Z_smul_mL X (hneg' _ _ h3) hz)) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (hneg' _ _ (h1 a)) (he a)
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (hneg' _ _ (h2 a)) (hf a)
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (hneg' _ _ (h4 l)) (hb l)
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (hneg' _ _ (h5 l)) (hbd l)

theorem Z_of_sym {u w : VA X.B.I} {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g (hA X.B.I w u - sigA X.B.I c)) : ZMod' X.B.I X.B.g (hA X.B.I u w - c) := by
  have hinv : ∀ t, sigA X.B.I (sigA X.B.I t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      first
        | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
        | (show TensorProduct.tmul X.B.I.F (X.B.I.cm.sig (X.B.I.cm.sig a)) b = TensorProduct.tmul X.B.I.F a b
           rw [show X.B.I.cm.sig (X.B.I.cm.sig a) = a from star_star a])
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hincl : ∀ e : X.B.I.E, sigA X.B.I (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) e) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (star e) := by
    intro e
    first
      | rfl
      | simp [sigA, Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]
  have hsym : hA X.B.I u w = sigA X.B.I (hA X.B.I w u) := by
    simp only [hA, Formalism.UG.hform, map_sum, map_mul, hinv, Matrix.map_apply, hincl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hJ : star (X.B.I.J i j) = X.B.I.J j i := by
      have e := congrFun (congrFun X.B.I.J_herm j) i
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at e
      exact e
    rw [hJ]
    ring
  have hInt : ∀ s ∈ IntAf X.B.I.F X.B.I.E, sigA X.B.I s ∈ IntAf X.B.I.F X.B.I.E := by
    have hle : IntAf X.B.I.F X.B.I.E ≤ (IntAf X.B.I.F X.B.I.E).comap (sigA X.B.I) := by
      show Subring.closure _ ≤ _
      rw [Subring.closure_le]
      rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inl ⟨⟨_, RingOfIntegers.mapRingEquiv (starRingAut : RingAut X.B.I.E) a, rfl⟩, ?_⟩)
        first
          | rfl
          | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
        simp [sigA, Formalism.UG.sigR]
    exact fun s hs => hle hs
  obtain ⟨t, ht, e⟩ := h
  refine ⟨sigA X.B.I t, hInt t ht, ?_⟩
  have e' : hA X.B.I w u = sigA X.B.I c + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := by
    rw [← e]
    ring
  rw [hsym, e', map_add, hinv, map_mul, map_natCast]
  ring

theorem Z0 {x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (h : ZMod' X.B.I X.B.g x) : ZMod' X.B.I X.B.g (x - 0) := by
  rw [sub_zero]
  exact h

theorem hA_bw_bw (l m : Fin D.R.k) : hA X.B.I (X.bw l) (X.bw m) = 0 := by
  have hsl : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I (s • x) y = sigA X.B.I s * hA X.B.I x y := by
    intro s x y
    simp only [hA, sigA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsr : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I x (s • y) = s * hA X.B.I x y := by
    intro s x y
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [X.bw_w l, X.bw_w m, hsl, hsr, ← mul_assoc, mul_comm (sigA X.B.I X.ew) X.ew, X.ew_orth, zero_mul]

theorem hA_bwd_bwd (l m : Fin D.R.k) : hA X.B.I (X.bwd l) (X.bwd m) = 0 := by
  have hsl : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I (s • x) y = sigA X.B.I s * hA X.B.I x y := by
    intro s x y
    simp only [hA, sigA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsr : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I x (s • y) = s * hA X.B.I x y := by
    intro s x y
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hinv : ∀ t, sigA X.B.I (sigA X.B.I t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      first
        | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
        | (show TensorProduct.tmul X.B.I.F (X.B.I.cm.sig (X.B.I.cm.sig a)) b = TensorProduct.tmul X.B.I.F a b
           rw [show X.B.I.cm.sig (X.B.I.cm.sig a) = a from star_star a])
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [X.bwd_w l, X.bwd_w m, hsl, hsr, hinv, ← mul_assoc, X.ew_orth, zero_mul]

theorem dual_coords {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : v - repr0 X v ∈ mL X.B.I X.B.g := by
  have hinv : ∀ t, sigA X.B.I (sigA X.B.I t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      first
        | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
        | (show TensorProduct.tmul X.B.I.F (X.B.I.cm.sig (X.B.I.cm.sig a)) b = TensorProduct.tmul X.B.I.F a b
           rw [show X.B.I.cm.sig (X.B.I.cm.sig a) = a from star_star a])
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have zsym : ∀ u w : VA X.B.I, ZMod' X.B.I X.B.g (hA X.B.I w u) → ZMod' X.B.I X.B.g (hA X.B.I u w - 0) := by
    intro u w h
    apply Z_of_sym X
    rw [map_zero, sub_zero]
    exact h
  have zz : ZMod' X.B.I X.B.g ((0 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - 0) := ⟨0, zero_mem _, by simp⟩
  have hmL : mL X.B.I X.B.g ≤ ReprSub X := by
    unfold mL
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    show _ - repr0 X _ ∈ mL X.B.I X.B.g
    rw [reference_repr_smul, ← smul_sub]
    unfold mL
    exact Submodule.subset_span ⟨x - repr0 X x, sub_mem hx (reference_repr_mem_lattice X hx), rfl⟩
  have hS : Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd ⊆ ReprSub X := by
    rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
    · refine T_gen X (X.e0 a) (fun a' => if a' = a then 1 else 0) 0 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp [ite_smul]
      · intro a'
        apply Z_of_sym X
        have e : sigA X.B.I (if a' = a then 1 else 0) = if a = a' then 1 else 0 := by
          by_cases h : a = a'
          · subst h
            simp
          · simp [h, Ne.symm h]
        rw [e]
        exact (X.gramIntegral a a').2.2
      · exact fun a' => Z0 X (X.gramIntegral a' a).1
      · exact zsym _ _ ((X.formsAtZero.2 a).1)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).2.2.1)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).1)
    · refine T_gen X (X.f0 a) 0 (fun a' => if a' = a then 1 else 0) 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp [ite_smul]
      · exact fun a' => Z0 X (X.gramIntegral a' a).2.1
      · exact fun a' => (X.gramIntegral a' a).2.2
      · exact zsym _ _ ((X.formsAtZero.2 a).2)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).2.2.2)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).2.1)
    · refine T_gen X X.z0 0 0 (-1) 0 0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp
      · exact fun a' => Z0 X ((X.formsAtZero.2 a').2)
      · exact fun a' => Z0 X ((X.formsAtZero.2 a').1)
      · rw [sub_neg_eq_add]
        exact X.formsAtZero.1
      · exact fun l => zsym _ _ ((X.weightVectorsIntegral l).2.1)
      · exact fun l => zsym _ _ ((X.weightVectorsIntegral l).1)
    · refine T_gen X (X.bw l) 0 0 0 (fun l' => if l' = l then X.ew else 0) 0 ?_ ?_ ?_ ?_ ?_ ?_
      · have hw := X.bw_w l
        simpa [ite_smul] using hw
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').2.1)
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').1)
      · exact Z0 X ((X.weightVectorsIntegral l).1)
      · exact fun l' => X.bw_dual l' l
      · intro l'
        rw [hA_bw_bw]
        exact zz
    · refine T_gen X (X.bwd l) 0 0 0 0 (fun l' => if l' = l then sigA X.B.I X.ew else 0) ?_ ?_ ?_ ?_ ?_ ?_
      · have hw := X.bwd_w l
        simpa [ite_smul] using hw
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').2.2.2)
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').2.2.1)
      · exact Z0 X ((X.weightVectorsIntegral l).2.1)
      · intro l'
        rw [hA_bwd_bwd]
        exact zz
      · intro l'
        apply Z_of_sym X
        have e : sigA X.B.I (if l' = l then sigA X.B.I X.ew else 0) = if l = l' then X.ew else 0 := by
          by_cases h : l = l'
          · subst h
            simp [hinv]
          · simp [h, Ne.symm h]
        rw [e]
        exact X.bw_dual l l'
  have hle : Submodule.span (IntAf X.B.I.F X.B.I.E)
      (Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd) ⊔ mL X.B.I X.B.g ≤ ReprSub X :=
    sup_le (Submodule.span_le.2 hS) hmL
  exact hle (X.latticeSpan v hv)

end Dual

end Formalism.L2.SG.NormCut
end
end

section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section Par

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hform_mulVec' {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have key : ∀ a b : n → A, Formalism.UG.hform σ J a b = ((fun i => σ (a i)) ᵥ* J) ⬝ᵥ b := by
    intro a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.vecMul, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hσ : (fun i => σ ((M *ᵥ x) i)) = (fun i => σ (x i)) ᵥ* (Formalism.UG.cT σ M) := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, map_mul]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [key, key, Matrix.dotProduct_mulVec, hσ, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hM]

theorem hA_unit (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I (X.B.I.fmat g *ᵥ x) (X.B.I.fmat g *ᵥ y) = hA X.B.I x y := by
  unfold hA
  refine hform_mulVec' _ _ (X.B.I.fmat g) ?_ x y
  exact g.2

theorem hA_adj (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I x (X.B.I.fmat g *ᵥ y) = hA X.B.I (X.B.I.fmat g⁻¹ *ᵥ x) y := by
  have e : X.B.I.fmat g *ᵥ (X.B.I.fmat g⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec]
    have h1 : X.B.I.fmat g * X.B.I.fmat g⁻¹ = 1 := by
      change X.B.I.fmat (g * g⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    rw [h1, Matrix.one_mulVec]
  calc hA X.B.I x (X.B.I.fmat g *ᵥ y) = hA X.B.I (X.B.I.fmat g *ᵥ (X.B.I.fmat g⁻¹ *ᵥ x)) (X.B.I.fmat g *ᵥ y) := by
        rw [e]
    _ = hA X.B.I (X.B.I.fmat g⁻¹ *ᵥ x) y := hA_unit X g _ y

theorem mem_mL_of_InAt {d : VA X.B.I} (hd : d ∈ X.B.I.Lf) (h : InAt X.B.I X.B.g X.B.g d) :
    d ∈ mL X.B.I X.B.g := by
  obtain ⟨c, hc, hcd⟩ := h
  have hb : ((c : ℤ) * Nat.gcdA c X.B.g + (X.B.g : ℤ) * Nat.gcdB c X.B.g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  have e : d = ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) +
      ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) := by
    rw [smul_smul, smul_smul, ← add_smul]
    have : ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
      have := congrArg (fun z : ℤ => (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) hb
      push_cast at this
      linear_combination this
    rw [this, one_smul]
  rw [e]
  have hint : ∀ z : ℤ, ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := fun z => intCast_mem _ z
  have sm : ∀ (z : ℤ) (w : VA X.B.I), w ∈ mL X.B.I X.B.g →
      ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w ∈ mL X.B.I X.B.g := fun z w hw => by
    have : ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w = (⟨_, hint z⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
    rw [this]; exact Submodule.smul_mem _ _ hw
  exact add_mem (sm _ _ hcd) (sm _ _ (smul_mem_mL X.B.I hd))

theorem mem_Mo_eb {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v))
    (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) (hb : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) v)) :
    v ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hv
  have e : v = (v - repr0 X v) + repr0 X v := by abel
  rw [e]
  refine add_mem (mL_Mo X.B.I hd) ?_
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      w ∈ Set.range X.e0 ∪ Set.range X.bw → c • w ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) :=
    fun c w hc hw => by
      have : c • w = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hw)
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF a) hv) (Or.inl ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))
  · exact mL_Mo X.B.I (Z_smul_mL X hz hZ)
  · exact sum_mem fun l _ => spn _ _ (hA_int X.B.I (hBd l) hv) (Or.inr ⟨l, rfl⟩)
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))

def Par (x : X.B.I.Gf) : Prop :=
  x ∈ X.B.I.Kset ∧ (∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) ∧
    ∀ j, X.B.I.fmat x *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw)

def Good (x : X.B.I.Gf) : Prop := Par X x ∧ Par X x⁻¹

theorem par_one : Par X 1 := by
  unfold Par Mo
  refine ⟨?_, fun a => ?_, fun j => ?_⟩
  · first
    | exact (Formalism.UG.stabGL X.B.I.Lf).one_mem
    | exact one_mem (Formalism.UG.stabGL X.B.I.Lf)
    | (show ((1 : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ Formalism.UG.stabGL X.B.I.Lf
       exact one_mem _)
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
    exact Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨j, rfl⟩))

theorem par_mul {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) : Par X (x * y) := by
  refine ⟨K_mul X.B.I hx.1 hy.1, fun a => ?_, fun j => ?_⟩
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.1 a)
    rintro _ ⟨b, rfl⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (hx.2.1 b) (sub_Mo X.B.I ⟨b, rfl⟩)
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0 ∪ Set.range X.bw) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.2 j)
    rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (Mo_mono X.B.I Set.subset_union_left (hx.2.1 b)) (sub_Mo X.B.I (Or.inl ⟨b, rfl⟩))
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (hx.2.2 l) (sub_Mo X.B.I (Or.inr ⟨l, rfl⟩))

theorem good_one : Good X 1 := by
  exact ⟨par_one X, by rw [inv_one]; exact par_one X⟩

theorem good_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : Good X (x * y) := by
  exact ⟨par_mul X hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact par_mul X hy.2 hx.2⟩

theorem good_inv {x : X.B.I.Gf} (hx : Good X x) : Good X x⁻¹ := by
  exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable {X} (TR : TypedRed X)

theorem leviM_mul_par {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v :=
  leviM_mul TR hx.1 hy.1 hy.2.2 hx.2.1 v

theorem leviM_one (v : TR.Pl) : leviM TR 1 v = 1 := by
  ext i j
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  simp only [leviM, show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
  have hI := hA_int X.B.I (hbwd i) (hbw j)
  rw [resT_of_mem TR v hI]
  have hZ := X.bw_dual i j
  have hIt : (if i = j then X.ew else 0) ∈ IntAf X.B.I.F X.B.I.E := by
    split_ifs
    · exact X.ew_int
    · exact zero_mem _
  have e : (⟨_, hI⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, sub_mem hI hIt⟩ + ⟨_, hIt⟩ := by
    apply Subtype.ext; simp
  rw [e, map_add, res_eq_zero_of_Z TR v _ hZ, zero_add]
  by_cases h : i = j
  · subst h
    simp only [if_true, Matrix.one_apply_eq]
    have e2 : (⟨X.ew, X.ew_int⟩ : IntAf X.B.I.F X.B.I.E) = ⟨X.ew * (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (one_mem _)⟩ := by apply Subtype.ext; simp
    have := TR.res_ew v 1
    simp only [OneMemClass.coe_one] at this
    convert this using 2
    exact (map_one (TR.res v)).symm
  · simp only [h, if_false, Matrix.one_apply_ne h]
    exact map_zero (TR.res v) |>.symm ▸ (by congr 1)

end Par

end Formalism.L2.SG.NormCut
end
end

section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section LeviHom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem leviM_mul_inv {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : leviM TR x v * leviM TR x⁻¹ v = 1 := by
  rw [← leviM_mul_par TR hx.1 hx.2 v, mul_inv_cancel, leviM_one]

theorem isUnit_det_leviM {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : IsUnit (leviM TR x v).det := by
  exact Matrix.isUnit_det_of_right_inverse (leviM_mul_inv TR hx v)

theorem levi_coe {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) :
    ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) = leviM TR x v := by
  unfold levi
  rw [dif_pos (isUnit_det_leviM TR hx v)]
  rfl

theorem levi_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : levi TR (x * y) = levi TR x * levi TR y := by
  funext v
  apply Units.ext
  rw [Pi.mul_apply, Units.val_mul, levi_coe TR (good_mul _ hx hy), levi_coe TR hx, levi_coe TR hy]
  exact leviM_mul_par TR hx.1 hy.1 v

theorem levi_one : levi TR (1 : X.B.I.Gf) = 1 := by
  funext v
  apply Units.ext
  rw [levi_coe TR (good_one _) v, leviM_one]
  rfl

theorem levi_inv {x : X.B.I.Gf} (hx : Good X x) : levi TR x⁻¹ = (levi TR x)⁻¹ := by
  have h1 := levi_mul TR (good_inv _ hx) hx
  rw [inv_mul_cancel, levi_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

end LeviHom

section ColGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem Z_hA_mL {d w : VA X.B.I} (hd : d ∈ mL X.B.I X.B.g) (hw : w ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I d w) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g (mL_Qs X.B.I X.B.g hw hd)

theorem colStab (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    (∀ a, X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.e0 a - X.e0 a ∈
      mL X.B.I X.B.g) ∧
    X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g := by
  set k := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) with hkdef
  obtain ⟨hE0, hF0, hZ0, -, -⟩ := frame_Lf X
  have hk' : k = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by rw [hkdef]; group
  have hfix : ∀ y ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u,
      X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y → X.B.I.fmat k *ᵥ incl X.B.I y = incl X.B.I y := by
    intro y hy hxu
    rw [hk']
    have h1 : X.B.I.fmat (h' : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y := h'.2 y hy
    have h2 : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I y = incl X.B.I y := fixes_inv X (h.2 y hy)
    exact fixes_mul X (fixes_inv X hxu) (fixes_mul X h2 (fixes_mul X h1 hxu))
  have hE : ∀ a, X.B.I.fmat k *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) := fun a =>
    hfix _ (Or.inl (Or.inl ⟨a, rfl⟩)) ((X.xu_fix u a).1)
  have hZ : X.B.I.fmat k *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u))) =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) := by
    rw [Matrix.mulVec_mulVec, ← fmat_mul]
    have e : k * (X.xu u)⁻¹ = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) := by rw [hkdef]; group
    rw [e, fmat_mul, ← Matrix.mulVec_mulVec]
    congr 1
    have hy : X.crd (X.zu u) ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u := Or.inr rfl
    exact fixes_mul X (fixes_inv X (h.2 _ hy)) (h'.2 _ hy)
  have key : ∀ (w v : VA X.B.I), v ∈ X.B.I.Lf → X.B.I.fmat k *ᵥ w = w → InAt X.B.I X.B.g X.B.g (v - w) →
      X.B.I.fmat k *ᵥ v - v ∈ mL X.B.I X.B.g := by
    intro w v hv hw hvw
    refine mem_mL_of_InAt X (sub_mem (K_mv X.B.I hk hv) hv) ?_
    have := congG_of_Kset X hk hvw
    have e : X.B.I.fmat k *ᵥ v - v = X.B.I.fmat k *ᵥ (v - w) - (v - w) := by
      rw [Matrix.mulVec_sub, hw]; abel
    rw [e]; exact this
  refine ⟨fun a => key _ _ (hE0 a) (hE a) (X.basisApprox a).1, key _ _ hZ0 hZ ?_⟩
  obtain ⟨c, hc, hcm⟩ := X.xu_z u
  refine ⟨c, hc, ?_⟩
  rw [show X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) =
    -(X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) - X.z0) by abel, smul_neg]
  exact Submodule.neg_mem _ hcm

theorem par_of_stab {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset)
    (he : ∀ a, X.B.I.fmat k *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hie : ∀ a, X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hiz : X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g) : Par X k := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hk, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat k *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k *ᵥ X.e0 a - X.e0 a) by abel]
    exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (mL_Mo X.B.I (he a))
  · refine mem_Mo_eb X (K_mv X.B.I hk (hB j)) (fun a => ?_) ?_ (fun l => ?_)
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a) by abel,
        hA_add_left]
      exact Z_add X.B.I X.B.g ((X.weightVectorsIntegral j).2.2 a).1 (Z_hA_mL X (hie a) (hB j))
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.z0 = X.z0 + (X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0) by abel, hA_add_left]
      exact Z_add X.B.I X.B.g (X.weightVectorsIntegral j).1 (Z_hA_mL X hiz (hB j))
    · have e : hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j) = 0 := by
        rw [X.bw_w l, X.bw_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
        have := X.ew_orth
        linear_combination (hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j)) * this
      rw [e]; exact Z_zero X.B.I X.B.g

theorem colGood (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset)
    (hki : ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    Good X (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by
  have e1 : (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) := by
    rw [_root_.mul_inv_rev, inv_inv]
  have e2 : (((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) := by
    rw [_root_.mul_inv_rev, inv_inv]
  obtain ⟨he, hz⟩ := colStab X u h h' hk
  obtain ⟨he', hz'⟩ := colStab X u h' h hki
  refine ⟨par_of_stab X hk he (by rw [e1]; exact he') (by rw [e1]; exact hz'), ?_⟩
  rw [e1]
  exact par_of_stab X hki he' (by rw [e2]; exact he) (by rw [e2]; exact hz)

end ColGood

section LeviColsPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

variable (F0 F0') in

def AdmPar : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    Good X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt)

theorem leviCols_of (hL : ColLatK cs) (hL' : ColLatK cs') (hA : AdmPar F0 F0' cs cs') :
    LeviCols TR F0 F0' cs cs' := by
  unfold LeviCols
  intro t ρ ρ' h1 h2
  have hK : Good X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt) := hA t
  unfold iotaOf scOf
  rw [h1, h2]
  unfold kOf at hK ⊢
  have lb : cs.lamOf (cs.base t.lam) = cs.lamOf ρ := by
    rw [h1]
    exact cs.base_lam _ (h1 ▸ cs.lam_mem ρ)
  have lb' : cs'.lamOf (cs'.base t.lam') = cs'.lamOf ρ' := by
    rw [h2]
    exact cs'.base_lam _ (h2 ▸ cs'.lam_mem ρ')
  have gA := colGood X u _ _ (hL _ _ lb) (hL _ _ lb.symm)
  have gB := colGood X u' _ _ (hL' _ _ lb') (hL' _ _ lb'.symm)
  have e : ((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * ((cs'.h ρ' : X.B.I.Gf) * X.xu u') =
      (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h ρ : X.B.I.Gf) * X.xu u))⁻¹ *
        (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 *
          ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) *
        (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h ρ' : X.B.I.Gf) * X.xu u')) := by
    group
  rw [e, levi_mul TR (good_mul _ (good_inv _ gA) hK) gB, levi_mul TR (good_inv _ gA) hK, levi_inv TR gA]

end LeviColsPf

end Formalism.L2.SG.NormCut
end
end

section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section NCongS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def NCong (x : X.B.I.Gf) : Prop :=
  (∀ a : Fin D.R.rS, (X.B.I.fmat x - 1) *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1})) ∧
    (X.B.I.fmat x - 1) *ᵥ X.z0 ∈ Mo X.B.I X.B.g (Set.range X.e0)

theorem ncong_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hnx : NCong X x) (hny : NCong X y) :
    NCong X (x * y) := by
  obtain ⟨hx1, hx2⟩ := hnx
  obtain ⟨hy1, hy2⟩ := hny
  refine ⟨fun a => ?_, ?_⟩
  · rw [mul_id]
    refine Submodule.add_mem _ ?_ (hx1 a)
    apply SE (hx := hx) (hc := hx1)
    exact hy1 a
  · rw [mul_id]
    refine Submodule.add_mem _ ?_ hx2
    apply SR (hx := hx) (hc := hx1)
    exact hy2

theorem Z_pair_Mo {w : VA X.B.I} (hw : w ∈ X.B.I.Lf) {S : Set (VA X.B.I)}
    (hS : ∀ s ∈ S, ZMod' X.B.I X.B.g (hA X.B.I w s)) :
    ∀ v ∈ Mo X.B.I X.B.g S, ZMod' X.B.I X.B.g (hA X.B.I w v) := by
  have hmL : mL X.B.I X.B.g ≤ Qs X.B.I X.B.g w := by
    apply mL_Qs
    exact hw
  have hle : Mo X.B.I X.B.g S ≤ Qs X.B.I X.B.g w :=
    sup_le (Submodule.span_le.mpr (fun s hs => hS s hs)) hmL
  exact fun v hv => hle hv

end NCongS

section K2iff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem res_ew_one (v : TR.Pl) : TR.res v ⟨X.ew, X.ew_int⟩ = 1 := by
  have h := TR.res_ew v 1
  rw [map_one] at h
  rw [← h]
  congr 1
  exact Subtype.ext (by simp)

theorem res_of_Z_delta (v : TR.Pl) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : c ∈ IntAf X.B.I.F X.B.I.E) (b : Prop)
    [Decidable b] (hZ : ZMod' X.B.I X.B.g (c - if b then X.ew else 0)) :
    TR.res v ⟨c, hc⟩ = if b then 1 else 0 := by
  set y : ↥(IntAf X.B.I.F X.B.I.E) := if b then ⟨X.ew, X.ew_int⟩ else 0 with hy
  have hyc : ((y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) = if b then X.ew else 0 := by
    rw [hy]
    split_ifs <;> rfl

  have hker : ∀ w, TR.res w (⟨c, hc⟩ - y) = 0 := by
    rw [TR.res_ker]
    obtain ⟨t, ht, hct⟩ := hZ
    refine ⟨X.ew * t, (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int ht, ?_⟩
    rw [AddSubgroupClass.coe_sub, hyc]
    show X.ew * (c - (if b then X.ew else 0)) = _
    rw [hct]
    ring
  have h := hker v
  rw [map_sub, sub_eq_zero] at h
  rw [h, hy]
  split_ifs
  · exact res_ew_one TR v
  · exact map_zero _

theorem bwc_ew (x : X.B.I.Gf) (j i : Fin D.R.k) :
    hA X.B.I (X.bwd j) (X.B.I.fmat x *ᵥ X.bw i) = X.ew * hA X.B.I (X.bwd j) (X.B.I.fmat x *ᵥ X.bw i) := by
  conv_lhs => rw [X.bwd_w j]
  rw [hA_smul_left, sigA_sigA]

private theorem leviM_apply_of_le_of_mem_K2 {x : X.B.I.Gf} (hk : x ∈ X.K2) (v : TR.Pl) :
    ∀ i j : Fin D.R.k, j ≤ i → leviM TR x v i j = if i = j then 1 else 0 := by
  obtain ⟨_, _, _, hc3⟩ := hk
  obtain ⟨_, _, hbe, hbb⟩ := Formalism.L2.SG.Pf.reference_frame_congruences (X := X)
  intro i j hji
  have hZ : ZMod' X.B.I X.B.g
      (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - if i = j then X.ew else 0) := by
    have e : X.B.I.fmat x *ᵥ X.bw j = X.bw j + (X.B.I.fmat x - 1) *ᵥ X.bw j := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [e, hA_add_right]
    have h1 := X.bw_dual i j
    have hsub : Set.range X.e0 ∪ X.bw '' {l | l.1 < j.1} ⊆ Set.range X.e0 ∪ X.bw '' {l | l.1 < i.1} :=
      Set.union_subset_union_right _ (Set.image_mono
        (fun l (hl : l.1 < j.1) => lt_of_lt_of_le hl (Fin.le_iff_val_le_val.mp hji)))
    have hmono : Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < j.1}) ≤
        Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < i.1}) := by
      apply Mo_mono
      exact hsub
    have hle : Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < i.1}) ≤ Qs X.B.I X.B.g (X.bwd i) := by
      apply Mb_Q <;> first | exact fun l => (X.vectorsInLattice.2.2 l).2 | exact hbe | exact hbb
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j)) :=
      hle (hmono (hc3 j))
    have h3 := Z_add X.B.I X.B.g h1 h2
    convert h3 using 1
    ring
  obtain ⟨t, ht, hct⟩ := hZ
  have hint : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E := by
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) =
        (if i = j then X.ew else 0) + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := by
      rw [← hct]
      ring
    rw [e]
    refine add_mem ?_ (mul_mem (natCast_mem _ _) ht)
    split_ifs
    · exact X.ew_int
    · exact zero_mem _
  show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j)) = _
  unfold resT
  rw [dif_pos hint]
  exact res_of_Z_delta TR v hint (i = j) ⟨t, ht, hct⟩

private theorem coe_levi_eq_leviM_of_mem_K2 {x : X.B.I.Gf} (hk : x ∈ X.K2) (v : TR.Pl) :
    ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) =
      leviM TR x v := by
  have hent := leviM_apply_of_le_of_mem_K2 TR hk v
  have hup : (leviM TR x v).BlockTriangular id := fun i j hij => by
    rw [hent i j hij.le, if_neg (ne_of_gt (show j < i from hij))]
  have hdet : (leviM TR x v).det = 1 := by
    rw [Matrix.det_of_upperTriangular hup]
    exact Finset.prod_eq_one (fun i _ => by rw [hent i i le_rfl, if_pos rfl])
  have hunit : IsUnit (leviM TR x v).det := by
    rw [hdet]
    exact isUnit_one
  simp only [levi, dif_pos hunit]
  rfl

theorem unitriangular_reduction_of_mem_level {x : X.B.I.Gf} (hx : Good X x) (hk : x ∈ X.K2) (v : TR.Pl) :
    Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR x v) := by
  have hent := leviM_apply_of_le_of_mem_K2 TR hk v
  have hlevi := coe_levi_eq_leviM_of_mem_K2 TR hk v
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [hlevi, hent i i le_rfl, if_pos rfl]
  · rw [hlevi, hent i j hji.le, if_neg (ne_of_gt hji)]

theorem mem_level_of_unitriangular {x : X.B.I.Gf} (hx : Good X x) (hn : NCong X x)
    (hu : ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR x v)) : x ∈ X.K2 := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hx.1.1, hn.1, hn.2, fun i => ?_⟩
  set w := X.B.I.fmat x *ᵥ X.bw i with hwdef
  have hwL : w ∈ X.B.I.Lf := K_mv X.B.I hx.1.1 (hB i)
  have hwM := hx.1.2.2 i
  have hd := dual_coords X hwL
  have hZe : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w) := fun a =>
    Z_pair_Mo X (hE0 a) (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · exact (X.gramIntegral a b).1
      · exact ((X.weightVectorsIntegral l).2.2 a).1) _ hwM
  have hZz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 w) :=
    Z_pair_Mo X hZ0 (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · rw [hA_symm]; exact Z_sig X.B.I X.B.g ((X.formsAtZero).2 b).1
      · exact (X.weightVectorsIntegral l).1) _ hwM
  have hbw0 : ∀ j, hA X.B.I (X.bw j) w = 0 := fun j => by
    rw [hwdef, X.bw_w j, X.bw_w i, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
    have := X.ew_orth
    linear_combination (hA X.B.I (X.bw j) (X.B.I.fmat x *ᵥ X.bw i)) * this

  have hcoef : ∀ j : Fin D.R.k, i.1 ≤ j.1 →
      ZMod' X.B.I X.B.g (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) := by
    intro j hij
    have hI := hA_int X.B.I (hBd j) hwL
    have hIt : ((if j = i then 1 else 0 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := by
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have hres : ∀ v, TR.res v ⟨_, sub_mem hI hIt⟩ = 0 := by
      intro v
      have hu' := hu v
      have hent : leviM TR x v j i = if j = i then 1 else 0 := by
        rw [← levi_coe TR hx]
        by_cases h : j = i
        · subst h; rw [if_pos rfl]; exact hu'.1 j
        · rw [if_neg h]; exact hu'.2 j i (lt_of_le_of_ne (Fin.le_def.2 hij) (fun e => h e.symm))
      have e : (⟨_, sub_mem hI hIt⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, hI⟩ - ⟨_, hIt⟩ := by
        apply Subtype.ext; simp
      rw [e, map_sub]
      have h1 : TR.res v ⟨_, hI⟩ = leviM TR x v j i := by
        show _ = resT TR v (hA X.B.I (X.bwd j) (X.B.I.fmat x *ᵥ X.bw i))
        rw [resT_of_mem TR v hI]
      rw [h1, hent]
      by_cases h : j = i
      · subst h
        have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 1 := by apply Subtype.ext; simp
        rw [if_pos rfl, this, map_one, sub_self]
      · have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 0 := by apply Subtype.ext; simp [h]
        rw [if_neg h, this, map_zero, sub_self]
    have hZ := (TR.res_ker ⟨_, sub_mem hI hIt⟩).1 hres
    have e : X.ew * (hA X.B.I (X.bwd j) w - if j = i then 1 else 0) =
        hA X.B.I (X.bwd j) w - if j = i then X.ew else 0 := by
      rw [mul_sub, ← bwc_ew x j i]
      split_ifs <;> ring
    simpa [e] using hZ

  have e1 : (X.B.I.fmat x - 1) *ᵥ X.bw i = (w - repr0 X w) +
      ((∑ a, hA X.B.I (X.f0 a) w • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) w • X.f0 a) - hA X.B.I X.z0 w • X.z0 +
        (∑ j, (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) • X.bw j) +
        (∑ j, hA X.B.I (X.bw j) w • X.bwd j)) := by
    have hbi : (∑ j, (if j = i then X.ew else 0) • X.bw j) = X.bw i := by
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact (X.bw_w i).symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hwdef]
    unfold repr0
    simp only [sub_smul, Finset.sum_sub_distrib, hbi]
    abel
  rw [e1]
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (s : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      s ∈ Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1} →
      c • s ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) := fun c s hc hs => by
    have : c • s = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • s := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hs)
  refine add_mem (mL_Mo X.B.I hd) (add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_)
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF0 a) hwL) (Or.inl ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (hZe a) (hF0 a))
  · exact mL_Mo X.B.I (Z_smul_mL X hZz hZ0)
  · refine sum_mem fun j _ => ?_
    by_cases hj : j.1 < i.1
    · have hne : j ≠ i := fun h => by subst h; exact lt_irrefl _ hj
      rw [if_neg hne, sub_zero]
      exact spn _ _ (hA_int X.B.I (hBd j) hwL) (Or.inr ⟨j, hj, rfl⟩)
    · exact mL_Mo X.B.I (Z_smul_mL X (hcoef j (not_lt.1 hj)) (hB j))
  · refine sum_mem fun j _ => ?_
    rw [hbw0, zero_smul]; exact zero_mem _

end K2iff

section ChiL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem chiL_eq_psiG {x : X.B.I.Gf} (hx : Good X x) (hk : x ∈ X.K2) : chiL X x = psiG TR (levi TR x) := by
  have hK : x ∈ X.B.I.Kset := hk.1
  have hint : ∀ i j : Fin D.R.k, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => hA_int X.B.I (X.vectorsInLattice.2.2 i).2 (K_mv X.B.I hK (X.vectorsInLattice.2.2 j).1)
  set C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := ∑ i : Fin D.R.k,
    if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0 with hC
  have hCint : C ∈ IntAf X.B.I.F X.B.I.E := by
    refine sum_mem (fun i _ => ?_)
    split_ifs
    · exact hint _ _
    · exact zero_mem _
  have hCew : C = X.ew * C := by
    rw [hC, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with h
    · exact bwc_ew x i ⟨i.1 + 1, h⟩
    · simp

  have hsum : ∀ v, TR.res v ⟨C, hCint⟩ = ∑ i : Fin D.R.k,
      (if h : i.1 + 1 < D.R.k then TR.res v ⟨_, hint i ⟨i.1 + 1, h⟩⟩ else 0) := by
    intro v
    have e : (⟨C, hCint⟩ : ↥(IntAf X.B.I.F X.B.I.E)) = ∑ i : Fin D.R.k,
        (if h : i.1 + 1 < D.R.k then (⟨_, hint i ⟨i.1 + 1, h⟩⟩ : ↥(IntAf X.B.I.F X.B.I.E)) else 0) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      show C = _
      rw [hC]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs <;> rfl
    rw [e, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  have hinner : ∀ (v : TR.Pl) (M : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) (i : Fin D.R.k),
      (∑ j : Fin D.R.k, if (j : ℕ) = (i : ℕ) + 1 then M i j else 0) =
        if h : i.1 + 1 < D.R.k then M i ⟨i.1 + 1, h⟩ else 0 := by
    intro v M i
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
      · simp
      · intro j _ hj
        rw [if_neg]
        intro hj'
        exact hj (Fin.ext hj')
      · simp
    · refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg]
      intro hj'
      have := j.2
      omega
  have hfac : ∀ v, Formalism.L2.SG.GGMirabolic.psiNat (TR.psi0 v) (levi TR x v) =
      TR.psi0 v (TR.res v ⟨C, hCint⟩) := by
    intro v
    unfold Formalism.L2.SG.GGMirabolic.psiNat
    rw [if_pos (unitriangular_reduction_of_mem_level TR hx hk v)]
    unfold Formalism.L2.SG.GGMirabolic.psiU
    rw [coe_levi_eq_leviM_of_mem_K2 TR hk v, hsum v]
    congr 1
    unfold Formalism.L2.SG.GGMirabolic.superdiag
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hinner v]
    split_ifs with h
    · show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩)) = _
      exact resT_of_mem TR v (hint i ⟨i.1 + 1, h⟩)
    · rfl
  unfold psiG
  simp only [hfac]
  rw [TR.psi_eq ⟨C, hCint⟩ hCew]
  rfl

end ChiL

section PhaseAtPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

variable (F0 F0') in

def AdmN : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    NCong X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt)

theorem ncong_colDiff (w : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w)
    (hk : ((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset) :
    NCong X (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) := by
  have s := colStab X w h h' hk
  refine ⟨fun a => ?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact mL_Mo X.B.I (s.1 a)
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact mL_Mo X.B.I s.2

private theorem ite_mem_K2_chiL_eq_psiG_levi {k : X.B.I.Gf} (gk : Good X k) (nk : NCong X k) :
    (if k ∈ X.K2 then chiL X k else 0) = psiG TR (levi TR k) := by
  by_cases hk2 : k ∈ X.K2
  · rw [if_pos hk2]
    exact chiL_eq_psiG TR gk hk2
  · rw [if_neg hk2]
    have hn : ¬ ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR k v) := fun hu => hk2 (mem_level_of_unitriangular TR gk nk hu)
    push_neg at hn
    obtain ⟨v, hv⟩ := hn
    unfold psiG
    refine (Finset.prod_eq_zero (Finset.mem_univ v) ?_).symm
    unfold Formalism.L2.SG.GGMirabolic.psiNat
    rw [if_neg hv]

theorem phaseAt_of (hL : ColLatK cs) (hL' : ColLatK cs') (hA : AdmPar F0 F0' cs cs') (hN : AdmN F0 F0' cs cs') :
    PhaseAt TR F0 F0' cs cs' := by
  unfold PhaseAt
  intro t ρ ρ' h1 h2
  have hK : Good X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt) := hA t
  have hNt : NCong X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt) :=
    hN t
  unfold kOf at hK hNt ⊢
  have lb : cs.lamOf (cs.base t.lam) = cs.lamOf ρ := by
    rw [h1]
    exact cs.base_lam _ (h1 ▸ cs.lam_mem ρ)
  have lb' : cs'.lamOf (cs'.base t.lam') = cs'.lamOf ρ' := by
    rw [h2]
    exact cs'.base_lam _ (h2 ▸ cs'.lam_mem ρ')
  have gA := colGood X u _ _ (hL _ _ lb) (hL _ _ lb.symm)
  have gB := colGood X u' _ _ (hL' _ _ lb') (hL' _ _ lb'.symm)
  have gAi : Good X (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)) := by
    have g := good_inv _ gA
    rwa [_root_.mul_inv_rev, inv_inv] at g
  have nAi := ncong_colDiff u (cs.h ρ) (cs.h (cs.base t.lam)) (hL _ _ lb.symm)
  have nB := ncong_colDiff u' (cs'.h (cs'.base t.lam')) (cs'.h ρ') (hL' _ _ lb')
  have e : ((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * ((cs'.h ρ' : X.B.I.Gf) * X.xu u') =
      (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)) *
        (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 *
          ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) *
        (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h ρ' : X.B.I.Gf) * X.xu u')) := by
    group
  have gk := good_mul _ (good_mul _ gAi hK) gB
  have nk := ncong_mul X (good_mul _ gAi hK).1.1 (ncong_mul X gAi.1.1 nAi hNt) nB
  rw [e]
  exact ite_mem_K2_chiL_eq_psiG_levi TR gk nk

end PhaseAtPf

end Formalism.L2.SG.NormCut
end
end

section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section GoodNC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ncong_inv {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) : NCong X x⁻¹ := by
  refine ⟨inv_e X.B.I X.B.g X.e0 hx hn.1, ?_⟩
  rw [inv_id]
  refine neg_mem (pres X.B.I (K_inv X.B.I hx) X.B.g _ _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ hn.2)
  rintro _ ⟨b, rfl⟩
  exact Mo_mono X.B.I (Set.image_subset_range _ _) (inv_e X.B.I X.B.g X.e0 hx hn.1 b)

theorem hermitian_module_beta_congruence {m : VA X.B.I} (hm : m ∈ Mo X.B.I X.B.g (Set.range X.e0)) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I m (X.bw j)) := by
  rw [hA_symm]
  refine Z_sig X.B.I X.B.g (Z_pair_Mo X (X.vectorsInLattice.2.2 j).1 ?_ _ hm)
  rintro _ ⟨a, rfl⟩
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral j).2.2 a).1

theorem par_of_ncong {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) (hni : NCong X x⁻¹) : Par X x := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hx, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat x *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat x - 1) *ᵥ X.e0 a by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel]
    exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (Mo_mono X.B.I (Set.image_subset_range _ _) (hn.1 a))
  · refine mem_Mo_eb X (K_mv X.B.I hx (hB j)) (fun a => ?_) ?_ (fun l => ?_)
    · rw [hA_adj]
      refine hermitian_module_beta_congruence X ?_ j
      rw [show X.B.I.fmat x⁻¹ *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat x⁻¹ - 1) *ᵥ X.e0 a by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel]
      exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (Mo_mono X.B.I (Set.image_subset_range _ _) (hni.1 a))
    · rw [hA_adj, show X.B.I.fmat x⁻¹ *ᵥ X.z0 = X.z0 + (X.B.I.fmat x⁻¹ - 1) *ᵥ X.z0 by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel, hA_add_left]
      exact Z_add X.B.I X.B.g (X.weightVectorsIntegral j).1 (hermitian_module_beta_congruence X hni.2 j)
    · have e : hA X.B.I (X.bw l) (X.B.I.fmat x *ᵥ X.bw j) = 0 := by
        rw [X.bw_w l, X.bw_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
        have := X.ew_orth
        linear_combination (hA X.B.I (X.bw l) (X.B.I.fmat x *ᵥ X.bw j)) * this
      rw [e]; exact Z_zero X.B.I X.B.g

theorem good_of_ncong {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) : Good X x := by
  have hni := ncong_inv X hx hn
  have hxi : x⁻¹ ∈ X.B.I.Kset := by
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hx ⊢
    simpa using inv_mem hx
  exact ⟨par_of_ncong X hx hn hni, par_of_ncong X hxi hni (by simpa using hn)⟩

end GoodNC

section AdmParPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

variable (F0 F0') in

def TermK : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt ∈ X.B.I.Kset

theorem adm_parity_of_norm (hK : TermK F0 F0' cs cs') (hN : AdmN F0 F0' cs cs') : AdmPar F0 F0' cs cs' := by
  intro t
  exact good_of_ncong _ (hK t) (hN t)

end AdmParPf

end Formalism.L2.SG.NormCut
end
end

section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section InAtAlg

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem natCast_mem_Int (c : ℕ) : ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := by
  exact natCast_mem _ c

theorem smul_mem_mL_int {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) {w : VA X.B.I}
    (hw : w ∈ mL X.B.I X.B.g) : s • w ∈ mL X.B.I X.B.g := by
  exact (mL X.B.I X.B.g).smul_mem ⟨s, hs⟩ hw

theorem InAt_add {a b : VA X.B.I} (ha : InAt X.B.I X.B.g X.B.g a) (hb : InAt X.B.I X.B.g X.B.g b) :
    InAt X.B.I X.B.g X.B.g (a + b) := by
  obtain ⟨c, hc, hca⟩ := ha
  obtain ⟨d, hd, hdb⟩ := hb
  refine ⟨c * d, Nat.Coprime.mul hc hd, ?_⟩
  have e : ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (a + b) =
      ((d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (((c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • a) +
        ((c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (((d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • b) := by
    rw [Nat.cast_mul, smul_add, ← mul_smul, ← mul_smul, mul_comm ((d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)]
  rw [e]
  exact (mL X.B.I X.B.g).add_mem (smul_mem_mL_int X (natCast_mem_Int X d) hca)
    (smul_mem_mL_int X (natCast_mem_Int X c) hdb)

theorem InAt_neg {a : VA X.B.I} (ha : InAt X.B.I X.B.g X.B.g a) : InAt X.B.I X.B.g X.B.g (-a) := by
  obtain ⟨c, hc, hca⟩ := ha
  exact ⟨c, hc, by rw [smul_neg]; exact (mL X.B.I X.B.g).neg_mem hca⟩

theorem InAt_sub {a b : VA X.B.I} (ha : InAt X.B.I X.B.g X.B.g a) (hb : InAt X.B.I X.B.g X.B.g b) :
    InAt X.B.I X.B.g X.B.g (a - b) := by
  rw [sub_eq_add_neg]
  exact InAt_add X ha (InAt_neg X hb)

theorem InAt_zero : InAt X.B.I X.B.g X.B.g 0 := by
  exact ⟨1, Nat.coprime_one_left _, by rw [smul_zero]; exact (mL X.B.I X.B.g).zero_mem⟩

theorem InAt_smul {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) {a : VA X.B.I}
    (ha : InAt X.B.I X.B.g X.B.g a) : InAt X.B.I X.B.g X.B.g (s • a) := by
  obtain ⟨c, hc, hca⟩ := ha
  exact ⟨c, hc, by rw [smul_comm]; exact smul_mem_mL_int X hs hca⟩

theorem InAt_sum {ι : Type} (t : Finset ι) (f : ι → VA X.B.I) (h : ∀ i ∈ t, InAt X.B.I X.B.g X.B.g (f i)) :
    InAt X.B.I X.B.g X.B.g (∑ i ∈ t, f i) := by
  exact Finset.sum_induction f (fun y => InAt X.B.I X.B.g X.B.g y) (fun _ _ => InAt_add X) (InAt_zero X) h

theorem InAt_K {κ : X.B.I.Gf} (hκ : κ ∈ X.B.I.Kset) {a : VA X.B.I} (ha : InAt X.B.I X.B.g X.B.g a) :
    InAt X.B.I X.B.g X.B.g (X.B.I.fmat κ *ᵥ a) := by
  obtain ⟨c, hc, h⟩ := ha
  exact ⟨c, hc, by rw [← Matrix.mulVec_smul]; exact mem_mL_of_Kset X hκ _ h⟩

theorem crd_add' (v w : (VS D).V) : X.crd (v + w) = X.crd v + X.crd w := by
  funext i
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

theorem crd_sub' (v w : (VS D).V) : X.crd (v - w) = X.crd v - X.crd w := by
  funext i
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

theorem crd_smul' (a : D.host.E) (v : (VS D).V) : X.crd (a • v) = X.ιE.symm a • X.crd v := by
  funext i
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

theorem crd_sum' {ι : Type} (t : Finset ι) (f : ι → (VS D).V) : X.crd (∑ i ∈ t, f i) = ∑ i ∈ t, X.crd (f i) := by
  funext i
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_sum, Finset.sum_apply]

theorem incl_sub' (x y : Fin X.B.I.n → X.B.I.E) : incl X.B.I (x - y) = incl X.B.I x - incl X.B.I y := by
  funext i
  simp [incl]

theorem incl_smul' (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (c • x) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) c • incl X.B.I x := by
  funext i
  simp [incl]

theorem incl_sum' {ι : Type} (t : Finset ι) (x : ι → Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (∑ j ∈ t, x j) = ∑ j ∈ t, incl X.B.I (x j) := by
  funext i
  simp [incl, map_sum, Finset.sum_apply]

theorem ratLink_incl {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x γ) (y : (VS D).V) :
    incl X.B.I (X.crd (γ y)) = X.B.I.fmat x.2 *ᵥ incl X.B.I (X.crd y) := by
  obtain ⟨M, -, -, hfm, hcrd⟩ := h
  rw [hcrd, hfm]
  funext i
  exact RingHom.map_mulVec _ _ _ i

theorem inclE_int (ξ : 𝓞 D.host.E) :
    Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (ξ : D.host.E)) ∈ IntAf X.B.I.F X.B.I.E := by
  refine inclE_mem X.B.I ?_
  have hint : IsIntegral ℤ (X.ιE.symm (ξ : D.host.E)) := by
    have := (ξ.2 : IsIntegral ℤ (ξ : D.host.E))
    exact this.map (X.ιE.symm.toRingHom.toIntAlgHom)
  exact ⟨⟨_, hint⟩, rfl⟩

end InAtAlg

section AdmNMain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def ModGAt : Prop :=
  ∀ (g1 : X.B.I.Gf) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    (∀ y, y ∈ Λ ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf) →
    ∀ v, ModG (VS D) Λ (gS D) v → InAt X.B.I X.B.g X.B.g (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v))

theorem frame_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (c : Fin (D.R.rS + 1)) : frame (mapLF γ F) c = γ (frame F c) := by
  unfold frame mapLF
  rw [dif_pos hγ]
  show (mapFlag γ hγ F.fl).fvec c = γ (F.fl.fvec c)
  simp only [FlagG.fvec, mapFlag]
  induction c using Fin.lastCases with
  | last => simp only [Fin.snoc_last]
  | cast i => simp only [Fin.snoc_castSucc]

theorem mulVec_fsum (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) {ι : Type}
    (t : Finset ι) (f : ι → VA X.B.I) : M *ᵥ (∑ i ∈ t, f i) = ∑ i ∈ t, M *ᵥ f i := by
  exact map_sum (Matrix.mulVecLin M) f t

variable {X} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

theorem adm_norm_of_fixed_frames (hTF : FrameTie X u u' F0 F0') (hK : TermK F0 F0' cs cs') (hM : ModGAt X) :
    AdmN F0 F0' cs cs' := by
  intro t
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  set g1 : X.B.I.Gf := (cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u with hg1
  set g2 : X.B.I.Gf := (cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u' with hg2
  have hκK := hK t
  set κ := kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt with hκ
  have hκ' : κ = g1⁻¹ * t.pt.2 * g2 := rfl
  have hb : cs.lamOf (cs.base t.lam) = t.lam := cs.base_lam _ t.mem
  have hRL : RatLink X t.pt t.lin := t.rep.2.1
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  obtain ⟨-, ⟨ξ, hξl, hξd, hξm⟩, -⟩ := t.rep.2.2.2.2
  have hlat : ∀ y, y ∈ t.lam ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := fun y => by
    rw [← hb]; exact cs.lat_eq _ y

  set s : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
    fun a c => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) with hs
  have hsI : ∀ a c, s a c ∈ IntAf X.B.I.F X.B.I.E := fun a c => inclE_int X (ξ a c)

  set Y : Fin (D.R.rS + 1) → VA X.B.I := fun a => X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (F0.fvec a)) with hY
  set Y' : Fin (D.R.rS + 1) → VA X.B.I := fun c => X.B.I.fmat g2⁻¹ *ᵥ incl X.B.I (X.crd (F0'.fvec c)) with hY'
  have key2 : ∀ c, InAt X.B.I X.B.g X.B.g (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a) := by
    intro c
    have h1 := hM g1 t.lam hlat _ (hξm c)
    erw [frame_mapLF hiso] at h1
    have e : X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (t.lin (frame (lf D F0') c) -
        frameAct (frame (lf D F0)) ξ c)) = X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a := by
      simp only [frameAct, crd_sub', crd_sum', crd_smul', incl_sub', incl_sum', incl_smul', Matrix.mulVec_sub,
        mulVec_fsum, Matrix.mulVec_smul, ratLink_incl X hRL]
      congr 1
      simp only [hY', Matrix.mulVec_mulVec, hκ', ← fmat_mul]
      congr 2
      group
    rw [e] at h1
    exact h1

  have fixE : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w) (a : Fin D.R.rS),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) :=
    fun w h a => fixes_inv X (fixes_mul X (h.2 _ (Or.inl (Or.inl ⟨a, rfl⟩))) ((X.xu_fix w a).1))
  have fixZ : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) =
        X.B.I.fmat (X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) := by
    intro w h
    have hz : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) = incl X.B.I (X.crd (X.zu w)) :=
      fixes_inv X (h.2 _ (Or.inr rfl))
    rw [_root_.mul_inv_rev, fmat_mul, ← Matrix.mulVec_mulVec, hz]
  set e0v : Fin (D.R.rS + 1) → VA X.B.I := Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 with he0v
  have hYa : ∀ a, InAt X.B.I X.B.g X.B.g (e0v a - Y a) := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, hY, Fin.snoc_last, FlagG.fvec, hTF.2.1, hg1, fixZ]
      have := InAt_neg X (X.xu_z u)
      rwa [neg_sub] at this
    · simp only [he0v, hY, Fin.snoc_castSucc, FlagG.fvec, hTF.1 i, hg1, fixE]
      exact (X.basisApprox i).1
  have hY'a : ∀ c, InAt X.B.I X.B.g X.B.g (e0v c - Y' c) := by
    intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [he0v, hY', Fin.snoc_last, FlagG.fvec, hTF.2.2.2, hg2, fixZ]
      have := InAt_neg X (X.xu_z u')
      rwa [neg_sub] at this
    · simp only [he0v, hY', Fin.snoc_castSucc, FlagG.fvec, hTF.2.2.1 i, hg2, fixE]
      exact (X.basisApprox i).1
  have he0vL : ∀ a, e0v a ∈ X.B.I.Lf := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, Fin.snoc_last]; exact hZ0
    · simp only [he0v, Fin.snoc_castSucc]; exact hE0 i
  have key4 : ∀ c, X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a ∈ mL X.B.I X.B.g := by
    intro c
    have hsm : ∀ (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), z ∈ IntAf X.B.I.F X.B.I.E → w ∈ X.B.I.Lf →
        z • w ∈ X.B.I.Lf := fun z w hz hw => by
      have : z • w = (⟨z, hz⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ hw
    refine mem_mL_of_InAt X (sub_mem (K_mv X.B.I hκK (he0vL c)) (sum_mem fun a _ => hsm _ _ (hsI a c) (he0vL a))) ?_
    have e : X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a =
        (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a) + X.B.I.fmat κ *ᵥ (e0v c - Y' c) -
          ∑ a, s a c • (e0v a - Y a) := by
      simp only [Matrix.mulVec_sub, smul_sub, Finset.sum_sub_distrib]; abel
    rw [e]
    exact InAt_sub X (InAt_add X (key2 c) (InAt_K X hκK (hY'a c)))
      (InAt_sum X _ _ fun a _ => InAt_smul X (hsI a c) (hYa a))

  have hsdiag : ∀ a, s a a = 1 := fun a => by simp [hs, hξd a]
  have hslow : ∀ a c, c < a → s a c = 0 := fun a c h => by simp [hs, hξl a c h]
  refine ⟨fun a => ?_, ?_⟩
  · have h4 := key4 (Fin.castSucc a)
    rw [Fin.sum_univ_castSucc, hslow (Fin.last _) (Fin.castSucc a) (Fin.castSucc_lt_last a), zero_smul,
      add_zero] at h4
    have e : (X.B.I.fmat κ - 1) *ᵥ X.e0 a = (X.B.I.fmat κ *ᵥ e0v (Fin.castSucc a) -
        ∑ i : Fin D.R.rS, s (Fin.castSucc i) (Fin.castSucc a) • e0v (Fin.castSucc i)) +
        ∑ i : Fin D.R.rS, (s (Fin.castSucc i) (Fin.castSucc a) - if i = a then 1 else 0) • X.e0 i := by
      simp only [he0v, Fin.snoc_castSucc, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [e]
    refine add_mem (mL_Mo X.B.I h4) (sum_mem fun i _ => ?_)
    by_cases hi : i.1 < a.1
    · have hne : i ≠ a := fun h => by subst h; exact lt_irrefl _ hi
      rw [if_neg hne, sub_zero]
      have : s (Fin.castSucc i) (Fin.castSucc a) • X.e0 i =
          (⟨_, hsI _ _⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 i := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨i, hi, rfl⟩)
    · by_cases hia : i = a
      · subst hia; rw [if_pos rfl, hsdiag, sub_self, zero_smul]; exact zero_mem _
      · have hlt : Fin.castSucc a < Fin.castSucc i := by
          rw [Fin.castSucc_lt_castSucc_iff]
          exact lt_of_le_of_ne (not_lt.1 hi) (fun h => hia h.symm)
        rw [if_neg hia, hslow _ _ hlt, sub_zero, zero_smul]; exact zero_mem _
  · have h4 := key4 (Fin.last _)
    rw [Fin.sum_univ_castSucc, hsdiag, one_smul] at h4
    have e : (X.B.I.fmat κ - 1) *ᵥ X.z0 = (X.B.I.fmat κ *ᵥ e0v (Fin.last _) -
        (∑ i : Fin D.R.rS, s (Fin.castSucc i) (Fin.last _) • e0v (Fin.castSucc i) + e0v (Fin.last _))) +
        ∑ i : Fin D.R.rS, s (Fin.castSucc i) (Fin.last _) • X.e0 i := by
      simp only [he0v, Fin.snoc_castSucc, Fin.snoc_last, Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [e]
    refine add_mem (mL_Mo X.B.I h4) (sum_mem fun i _ => ?_)
    have : s (Fin.castSucc i) (Fin.last _) • X.e0 i = (⟨_, hsI _ _⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨i, rfl⟩)

end AdmNMain

end Formalism.L2.SG.NormCut
end
end
