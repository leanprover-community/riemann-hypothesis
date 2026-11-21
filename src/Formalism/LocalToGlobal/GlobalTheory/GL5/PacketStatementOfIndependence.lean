import Formalism.LocalToGlobal.GlobalTheory.ConcTop
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJClassFin
import Formalism.PeriodIntegrals.UJClassMassAlt
import Formalism.PeriodIntegrals.MassRankOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.AdelicBounds
import Formalism.LocalToGlobal.GlobalTheory.GL5.LocalEndomorphismContinuous
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountRec
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryClassMassHermitian

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Triv

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem isLattice_of_subsingleton [Subsingleton V] (L : Submodule (𝓞 K) V) : Submodule.IsLattice K L := by
  have hL : L = ⊥ := Subsingleton.elim _ _
  refine ⟨?_, ?_⟩
  · rw [hL]; exact Submodule.fg_bot
  · exact Subsingleton.elim _ _

theorem mass_of_subsingleton [Subsingleton V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.mass h L = 1 := by
  classical
  have hsub : ∀ M N : Submodule (𝓞 K) V, M = N := fun M N => Subsingleton.elim _ _
  have hgen : L ∈ Formalism.HermitianLatticesTheory.genus h L :=
    ⟨isLattice_of_subsingleton L, fun p _ => ⟨1, one_mem _, hsub _ _⟩⟩
  have hreps : Formalism.ThetaLiftIndependence.IsClassReps h L {L} := by
    refine ⟨fun M hM => ?_, fun M _ => ⟨L, ⟨Finset.mem_singleton_self _, 1, one_mem _, hsub _ _⟩, ?_⟩⟩
    · rw [Finset.mem_singleton] at hM; rw [hM]; exact hgen
    · intro N hN; exact Finset.mem_singleton.mp hN.1
  have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨_, hreps⟩
  have hmem : L ∈ hex.choose := by
    obtain ⟨N, ⟨hN, -⟩, -⟩ := hex.choose_spec.2 L hgen
    rwa [hsub N L] at hN
  have heq : hex.choose = {L} := by
    ext M
    rw [Finset.mem_singleton]
    constructor
    · intro _; exact hsub _ _
    · rintro rfl; exact hmem
  have haut : Nat.card (Formalism.ThetaLiftIndependence.autL h L) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext (LinearEquiv.ext fun x => Subsingleton.elim _ _)⟩,
      ⟨⟨1, one_mem _, hsub _ _⟩⟩⟩
  unfold Formalism.HermitianLatticesTheory.mass
  rw [dif_pos hex, heq, Finset.sum_singleton, haut]
  simp

end Triv

theorem subsingleton_of_rank_zero {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E)
    (hrk : W.rank = 0) : Subsingleton W.V := by
  have : IsEmpty (Fin W.rank) := by rw [hrk]; infer_instance
  exact W.frame.repr.toEquiv.subsingleton

theorem subsingleton_HA_zero {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hM : M = 0) : Subsingleton (HA R σ J) := by
  subst hM
  refine ⟨fun a b => ?_⟩
  let a' : HR R σ J := a
  let b' : HR R σ J := b
  have e : (a' : GL (Fin 0) (R ⊗[F] E)) = (b' : GL (Fin 0) (R ⊗[F] E)) :=
    Units.ext (Matrix.ext fun i _ => Fin.elim0 i)
  exact Subtype.ext e

theorem genusMassAt_zero (D : D7) : GenusMassAt D 0 := by
  intro W _ _ hrk
  have := subsingleton_of_rank_zero W hrk
  rw [mass_of_subsingleton]
  unfold massI
  rw [mass_of_subsingleton]

theorem classFinAt_zero (D : D7) : ClassFinAt D 0 := by
  intro W _ _ hrk
  have := subsingleton_HA_zero (AF D.host.F) D.sp.cm.sig W.gram hrk
  exact ⟨1, fun _ => 1, fun x => ⟨0, 1, 1, Subsingleton.elim _ _⟩, fun i j _ _ _ _ _ => Subsingleton.elim i j⟩

theorem classMassAt_zero (D : D7) : ClassMassAt D 0 := by
  intro W _ _ hrk m g hcov hdisj
  have := subsingleton_of_rank_zero W hrk
  have := subsingleton_HA_zero (AF D.host.F) D.sp.cm.sig W.gram hrk
  obtain ⟨i0, -⟩ := hcov 1
  have : Unique (Fin m) := ⟨⟨i0⟩, fun j => hdisj j i0 1 1 1 1 (Subsingleton.elim _ _)⟩
  have hc : Nat.card (Unfold.stab (GamA D W) (StabFin.SFin D.sp.cm.sig W.gram (L0c D W)) (g i0)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext (Subsingleton.elim _ _))⟩, ⟨⟨1, ?_⟩⟩⟩
    have e : (g i0)⁻¹ * (((1 : GamA D W) : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i0) = 1 :=
      Subsingleton.elim _ _
    show (g i0)⁻¹ * (((1 : GamA D W) : HA (AF D.host.F) D.sp.cm.sig W.gram) * g i0) ∈
      StabFin.SFin D.sp.cm.sig W.gram (L0c D W)
    rw [e]
    exact (StabFin.SFin D.sp.cm.sig W.gram (L0c D W)).one_mem
  rw [mass_of_subsingleton, Fintype.sum_unique, show (default : Fin m) = i0 from Subsingleton.elim _ _, hc]
  simp

theorem classItemsAt_zero (D : D7) : ClassItemsAt D 0 :=
  ⟨genusMassAt_zero D, classFinAt_zero D, classMassAt_zero D⟩

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem volume_mass_of_low_ranks (D : D7) (hT : VolTie D) (hV : VolRatioTrue D) (hI1 : ClassItemsAt D 1)
    (hI2 : ClassItemsAt D 2) : VolumeEqMass₂ D :=
  volume_mass_of_items D hT hV (classItemsAt_zero D) hI1 hI2

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassMass Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem crd_smul_mem {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (r : 𝓞 E) {x : Fin M → E} (hx : x ∈ crdOf b L0) :
    (r : E) • x ∈ crdOf b L0 := by
  show ∑ i, ((r : E) • x) i • b i ∈ L0
  have e : ∑ i, ((r : E) • x) i • b i = r • ∑ i, x i • b i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_smul, algebraMap_smul]
  rw [e]
  exact L0.smul_mem r hx

theorem latHat_smul {M : ℕ} (L : Set (Fin M → E)) (hL : ∀ r : 𝓞 E, ∀ x ∈ L, (r : E) • x ∈ L) (r : 𝓞 E)
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E L) :
    inclR (F := F) (Af F) (r : E) • y ∈ latHat F E L := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, (r : E) • x, hL r x hx, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
    show (1 : Af F) ⊗ₜ[F] (r : E) * a ⊗ₜ[F] x i = a ⊗ₜ[F] ((r : E) * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg y _ h1 => rw [smul_neg]; exact neg_mem h1

theorem vinc_zero {M : ℕ} : PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (0 : Fin M → E) = 0 := by
  funext i; exact map_zero _

theorem vinc_add {M : ℕ} (x y : Fin M → E) :
    PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (x + y) = PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x + PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y := by
  funext i; exact map_add _ _ _

theorem vinc_smul {M : ℕ} (c : E) (x : Fin M → E) :
    PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (c • x) = inclR (F := F) (Af F) c • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x := by
  funext i; exact map_mul _ _ _

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def lamSub (L : Set (Fin M → E)) (hL : ∀ r : 𝓞 E, ∀ x ∈ L, (r : E) • x ∈ L) (g : HA (AF F) σ J) :
    Submodule (𝓞 E) (Fin M → E) where
  carrier := PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L g
  zero_mem' := by
    show (finMat σ J g⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) 0) ∈ latHat F E L
    rw [vinc_zero, Matrix.mulVec_zero]; exact zero_mem _
  add_mem' := by
    intro x y hx hy
    show (finMat σ J g⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (x + y)) ∈ latHat F E L
    rw [vinc_add, Matrix.mulVec_add]; exact add_mem hx hy
  smul_mem' := by
    intro r x hx
    show (finMat σ J g⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (r • x)) ∈ latHat F E L
    have e : r • x = (r : E) • x := by funext i; exact Algebra.smul_def r (x i)
    rw [e, vinc_smul, Matrix.mulVec_smul]
    exact latHat_smul L hL r hx

end Gen

def LatGenus : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g : HA (AF F) σ (gramOf h b)) (N : Submodule (𝓞 E) V),
      (N : Set V) = latSet σ (gramOf h b) b L0 g → Submodule.IsLattice E N → SameGenus h L0 N

theorem latLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b), ∃ N : Submodule (𝓞 E) V,
      (N : Set V) = latSet σ (gramOf h b) b L0 g ∧ Submodule.IsLattice E N := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hτ hL hsig g
  classical
  have hcrd := crdBounds F E V M b L0 hL
  obtain ⟨D, T, c0, hD, hT, hc0, hall⟩ :=
    PI.UnitaryGroupMassFormula.UJClassFin.adelic_bounds F E σ M (gramOf h b) (crdOf b L0) hσ hτ hsig hcrd.1 hcrd.2
  obtain ⟨-, ⟨k, hk0, hlow⟩, hint, -⟩ := hall g
  have hLs : ∀ r : 𝓞 E, ∀ x ∈ crdOf b L0, (r : E) • x ∈ crdOf b L0 := fun r x hx => crd_smul_mem b L0 r hx
  let Nc := lamSub σ (gramOf h b) (crdOf b L0) hLs g
  let e' : V ≃ₗ[𝓞 E] (Fin M → E) := b.equivFun.restrictScalars (𝓞 E)
  let N : Submodule (𝓞 E) V := Nc.comap e'.toLinearMap
  refine ⟨N, rfl, ?_, ?_⟩
  ·

    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hPD := PI.UnitaryGroupMassFormula.UJClassFin.posDefOfDefiniteSignature_holds M _ (hsig τ)
    have hdet : (gramOf h b).det ≠ 0 := by
      intro h0
      have : ((gramOf h b).map τ).det = 0 := by
        rw [show (gramOf h b).map τ = τ.mapMatrix (gramOf h b) from rfl, ← RingHom.map_det, h0, map_zero]
      exact hPD.det_pos.ne' this
    have hu : IsUnit (gramOf h b).det := isUnit_iff_ne_zero.mpr hdet
    obtain ⟨d, hd0, hdint⟩ := PI.UnitaryGroupMassFormula.UJClassFin.mat_den (gramOf h b)⁻¹
    have hJy : ∀ y ∈ Nc, ∀ i, IsIntegral ℤ ((D : E) * (k : E) * ((gramOf h b).mulVec y) i) := by
      intro y hy i
      have h1 := hint _ (hlow i 1 isIntegral_one) y hy
      have e : PI.HermLatFin.herm (σ : E →+* E) (gramOf h b) (Pi.single i ((k : E) * 1)) y =
          (k : E) * ((gramOf h b).mulVec y) i := by
        unfold PI.HermLatFin.herm
        rw [Finset.sum_eq_single i]
        · simp only [Pi.single_eq_same, mul_one, map_natCast, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
        · intro j _ hj
          simp [Pi.single_eq_of_ne hj]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [e, ← mul_assoc] at h1
      exact h1
    have hy_eq : ∀ y : Fin M → E, y = ((gramOf h b)⁻¹).mulVec ((gramOf h b).mulVec y) := by
      intro y
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    have hfgc : Nc.FG := by
      refine PI.UnitaryGroupMassFormula.UJClassFin.fg_of_den Nc (d * D * k) (by positivity) fun y hy j => ?_
      have hyj : y j = ∑ i, (gramOf h b)⁻¹ j i * ((gramOf h b).mulVec y) i := by
        conv_lhs => rw [hy_eq y]
        rfl
      rw [hyj, Finset.mul_sum]
      refine IsIntegral.sum _ fun i _ => ?_
      have e : ((d * D * k : ℕ) : E) * ((gramOf h b)⁻¹ j i * ((gramOf h b).mulVec y) i) =
          ((d : E) * (gramOf h b)⁻¹ j i) * ((D : E) * (k : E) * ((gramOf h b).mulVec y) i) := by
        push_cast; ring
      rw [e]
      exact (hdint j i).mul (hJy y hy i)
    have hN : N = Nc.map e'.symm.toLinearMap := Submodule.comap_equiv_eq_map_symm e' Nc
    rw [hN]
    exact hfgc.map _
  ·
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hk : (k : E) ≠ 0 := by exact_mod_cast hk0.ne'
    have hmem : (k : E) • b i ∈ N := by
      show b.equivFun ((k : E) • b i) ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g
      have e : b.equivFun ((k : E) • b i) = Pi.single i ((k : E) * 1) := by
        funext j
        rw [map_smul, Pi.smul_apply, Module.Basis.equivFun_apply, b.repr_self, Finsupp.single_apply,
          Pi.single_apply, smul_eq_mul]
        split_ifs <;> simp_all
      rw [e]
      exact hlow i 1 isIntegral_one
    have e2 : b i = (k : E)⁻¹ • ((k : E) • b i) := by rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem latStep_of (hG : LatGenus) : LatStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hsymm hnd hL hsig g
  obtain ⟨N, hNs, hNl⟩ := latLattice F E σ V h M b L0 hσ hτ hL hsig g
  exact ⟨N, hNs, hNl, hG F E σ V h M b L0 hσ hθ hτ hsymm hnd hL hsig g N hNs hNl⟩

theorem uJClassMass_of_genus (hG : LatGenus) (hS : SurjStep) : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_open (latStep_of hG) hS

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_sig_ne (D : D7) : ∃ θ : D.host.E, D.sp.cm.sig θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.host.E)
  obtain ⟨θ, t, e, h⟩ := D.sp.cm.cmUnram.2.2 P hP
  refine ⟨algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ, fun h' => h ?_⟩
  have h'' : star (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ) =
      algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ := h'
  rw [h''] at e
  have : t = θ := NumberField.RingOfIntegers.coe_injective e
  rw [this, sub_self]
  exact P.zero_mem

theorem classFin_of_UJ (hF : PI.UJClassFin.UJClassFin) (D : D7) : ClassFin D := by
  intro W hW hsig
  exact hF D.host.F D.host.E D.sp.cm.sig W.rank W.gram (L0c D W) (fun _ => rfl)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1)
    (StabFin.crd_up (F := D.host.F) W) (StabFin.crd_low (F := D.host.F) W)

theorem class_number_finite (D : D7) : ClassFin D := classFin_of_UJ unitary_class_set_finite D

theorem class_number_finite_rank (D : D7) (n : ℕ) : ClassFinAt D n := classFinAt_of D (class_number_finite D) n

theorem class_mass_of_genus_classes (hM : PI.UJClassMass2.UJClassMass) (D : D7) : ClassMass D := by
  intro W hW hsig n g hcov hdisj
  exact hM D.host.F D.host.E D.sp.cm.sig W.V W.hT W.rank W.frame W.L0 (fun _ => rfl) (exists_sig_ne D)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) W.herm W.nondeg W.standardTuple_isLattice
    (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1) n g hcov hdisj

theorem classMass_of_steps (hG : ClassSteps.LatGenus) (hS : PI.UnitaryGroupMassFormula.UJClassMass.SurjStep) (D : D7) : ClassMass D :=
  class_mass_of_genus_classes (ClassSteps.uJClassMass_of_genus hG hS) D




theorem isIntegralLat_of_unimod {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) :
    Formalism.HermitianLatticesTheory.IsIntegralLat W.hT W.L0 := by
  intro x hx y hy
  have hd : y ∈ Formalism.HermitianLatticesTheory.dual W.hT W.L0 := by rw [W.baseLattice_isUnimodular]; exact hy
  have h1 := (Submodule.mem_iInf _).1 hd x
  exact (Submodule.mem_iInf _).1 h1 hx

theorem isPosDef_of_sig (D : D7) (W : HSpace D.host.E) (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0)) :
    PI.MassRankOne.IsPosDef W.hT := by
  intro τ x hx
  obtain ⟨c, hc, e⟩ := W.form_pos hW τ (D.sp.cm.cmUnram.2.1 τ) (hsig τ) x hx
  rw [e, Complex.ofReal_re]
  exact hc

theorem genusMassAt_one_of (hR : PI.MassRankOne.MassRankOne) (D : D7) : GenusMassAt D 1 := by
  intro W hW hsig hrk
  unfold massI
  exact hR D.host.E D.sp.cm.cmUnram W.V (Fin 1 → D.host.E) W.hT (stdForm D.host.E 1) W.L0
    (stdLat D.host.E 1) W.herm (isPosDef_of_sig D W hW hsig) (W.rank_eq.trans hrk) W.standardTuple_isLattice
    (isIntegralLat_of_unimod W) (Formalism.HermitianLattices.Ext.L3.stdForm_isSymm D.host.E 1)
    (Formalism.HermitianLattices.Ext.L3.stdLat_isOrtho D.host.E 1)

theorem classItemsAt_of_UJ (hM : PI.UJClassMass2.UJClassMass) (D : D7) (n : ℕ) (hG : GenusMassAt D n) :
    ClassItemsAt D n :=
  ⟨hG, class_number_finite_rank D n, classMassAt_of D (class_mass_of_genus_classes hM D) n⟩

theorem classItemsAt_one_of_UJ (hR : PI.MassRankOne.MassRankOne) (hM : PI.UJClassMass2.UJClassMass) (D : D7) :
    ClassItemsAt D 1 :=
  classItemsAt_of_UJ hM D 1 (genusMassAt_one_of hR D)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem volume_eq_mass_of_genus (D : D7) (hT : VolTie D) (hV : VolRatioTrue D) (hG2 : GenusMassAt D 2)
    (hM : PI.UJClassMass2.UJClassMass) : BaseVolumeEqualsMass D :=
  volume_eq_mass_of_ratio D hT hV (classItemsAt_of_UJ hM D 2 hG2)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem volume_mass_indefinite_genus (D : D7) (hT : VolTie D) (hV : VolRatioTrue D) (hG2 : GenusMassAt D 2)
    (hR : PI.MassRankOne.MassRankOne) (hM : PI.UJClassMass2.UJClassMass) : VolumeEqMass₂ D :=
  volume_mass_of_low_ranks D hT hV (classItemsAt_one_of_UJ hR hM D) (classItemsAt_of_UJ hM D 2 hG2)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.ConcTop

def RowRec (𝒞 : FamClass) (P : D7 → Prop) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), P (Fm.D x i)

def RowCount (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => FamilyMassVolumeBounds Fm → FamilyLevelConditionAdmitted Fm →
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev

def RowClsTie (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Nonempty (Formalism.MainNotions.Gaps.CC.ClsTie (Fm.D x i))

section LH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem landherrHasse_of_sig (D : D7) (hL : LandherrSig D) : LandherrHasse D := by
  intro W hW hsig
  obtain ⟨φ, hφ⟩ := hL (stdPos D W.rank) W (stdPos_sigOK D W.rank) hW (stdPos_rank D W.rank)
    (fun τ => by rw [stdPos_sig, hsig])
  refine ⟨fun a => φ ((stdPos D W.rank).frame a), ?_, fun a c => ?_⟩
  · exact (stdPos D W.rank).frame.linearIndependent.map' φ.toLinearMap φ.ker
  · rw [hφ]
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (fun x hx => Formalism.BasicNotions.Examples₂.star_isIntegral x hx) W.rank
      (fun _ => false) W.rank 0 a c).trans ?_
    simp [Formalism.BasicNotions.Examples₂.sgn]

end LH

theorem classItemsAt_all (D : D7) (hG : GenusMassStd D) (hM : ClassMass D) (n : ℕ) : ClassItemsAt D n :=
  ⟨genusMassAt_of D hG n, class_number_finite_rank D n, classMassAt_of D hM n⟩

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem stmtF_of_named {eps : ℝ} (Fm : FamP eps) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : ∀ x (i : Fm.Ix x), Formalism.L2.Theta.RealTied (Fm.D x i))
    (hW : WeilSiegelCM)
    (hV : ∀ x (i : Fm.Ix x), VolSigIndep (Fm.D x i))
    (hM : ∀ x (i : Fm.Ix x), ClassMass (Fm.D x i))
    (hHC : ∀ x (i : Fm.Ix x), HCFormalDegree (Fm.D x i))
    (hL : ∀ x (i : Fm.Ix x), LandherrSig (Fm.D x i))
    (hG : ∀ x (i : Fm.Ix x), GenusMassStd (Fm.D x i))
    (hN : FamilyMassVolumeBounds Fm → FamilyLevelConditionAdmitted Fm → ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev) :
    KudlaFamilyStatement Fm C3 :=
  stmtF_of_open Fm C3 (by linarith) (siegel_weil_part_one_of_weil_theorem eps Fm hW)
    (fun _ => standardMassRatio_of_modelMassRatio Formalism.HermitianLattices.SiegelMassBounds.siegel_mass_ratio)
    (fun _ hT x i => ⟨theorem_two_of_landherr (Fm.D x i) (hT x i) (hV x i) (hL x i)
        (fun n _ => classItemsAt_all (Fm.D x i) (hG x i) (hM x i) n),
      volume_mass_of_class_items (Fm.D x i) (hT x i) (hG x i) (class_number_finite (Fm.D x i)) (hM x i)⟩)
    (fun hA x i => theorem_three_all_unitary (Fm.D x i) C3 hC3 (hR x i).cdScale (hHC x i) (hA x i).2.2)
    (fun x hx i => levels_pro_g (Fm.D x i) (Fm.ex x hx i).lev)
    hN
    (fun x i => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.landherrSmall_of_hasse (Fm.D x i) (landherrHasse_of_sig (Fm.D x i) (hL x i)))

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_named (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞)
    (hW : WeilSiegelCM)
    (hV : RowRec 𝒞 VolSigIndep)
    (hM : RowRec 𝒞 ClassMass)
    (hHC : RowRec 𝒞 HCFormalDegree)
    (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd)
    (hN : RowCount 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  (((((hR.and hV).and hM).and hHC).and hL).and (hG.and hN)).imp
    fun Fm _ _ h => stmtF_of_named Fm C3 hC3 h.1.1.1.1.1 hW h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2.1 h.2.2

theorem rowRec_of_all {𝒞 : FamClass} {P : D7 → Prop} (hP : ∀ D, P D) (hR : RowReal 𝒞) : RowRec 𝒞 P :=
  hR.imp fun Fm _ _ _ x i => hP (Fm.D x i)

theorem rowCount_of_clsTie {𝒞 : FamClass} (h : RowClsTie 𝒞) : RowCount 𝒞 :=
  h.imp fun Fm _ _ h _ _ x hx i => (h x hx i).elim fun X => Formalism.MainNotions.Gaps.CC.class_number_of_class_data X (Fm.ex x hx i).lev

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_genus_classes (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞) (hW : WeilSiegelCM) (hV : RowRec 𝒞 VolSigIndep)
    (hUJ : PI.UJClassMass2.UJClassMass)
    (hHC : RowRec 𝒞 HCFormalDegree) (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd) (hX : RowClsTie 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  packet_statement_of_named 𝒞 C3 hC3 hR hW hV (rowRec_of_all (class_mass_of_genus_classes hUJ) hR) hHC hL hG (rowCount_of_clsTie hX)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_surjection (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞) (hW : WeilSiegelCM) (hV : RowRec 𝒞 VolSigIndep)
    (hLG : ClassSteps.LatGenus) (hSS : PI.UnitaryGroupMassFormula.UJClassMass.SurjStep)
    (hHC : RowRec 𝒞 HCFormalDegree) (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd) (hX : RowClsTie 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  packet_statement_of_named 𝒞 C3 hC3 hR hW hV (rowRec_of_all (classMass_of_steps hLG hSS) hR) hHC hL hG (rowCount_of_clsTie hX)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem genus_class_mass : PI.UJClassMass2.UJClassMass := _root_.unitary_class_mass_hermitian

theorem classMass_of_D7 (D : D7) : ClassMass D := class_mass_of_genus_classes genus_class_mass D




theorem volume_mass_of_genus_rank (D : D7) (n : ℕ) (hT : VolTie D) (hG : GenusMassAt D n) : volumeAtLevelZero D n :=
  volume_mass_of_class_data D n hT hG (class_number_finite_rank D n) (classMassAt_of D (classMass_of_D7 D) n)



end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.ConcTop

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_independence (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞)
    (hW : WeilSiegelCM)
    (hV : RowRec 𝒞 VolSigIndep)
    (hHC : RowRec 𝒞 HCFormalDegree)
    (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd)
    (hN : RowCount 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  packet_statement_of_named 𝒞 C3 hC3 hR hW hV (rowRec_of_all Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.classMass_of_D7 hR) hHC hL hG hN

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_class_count (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞) (hW : WeilSiegelCM) (hV : RowRec 𝒞 VolSigIndep)
    (hHC : RowRec 𝒞 HCFormalDegree) (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd) (hX : RowClsTie 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  packet_statement_of_independence 𝒞 C3 hC3 hR hW hV hHC hL hG (rowCount_of_clsTie hX)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

end
end
