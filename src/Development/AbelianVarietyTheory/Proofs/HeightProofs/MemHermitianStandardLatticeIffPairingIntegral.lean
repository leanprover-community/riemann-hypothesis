import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ShiftMapsUpDown
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsResolution

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.WeilUnramifiedCompare

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_coord (V : HSpace E) (x y : Fin V.rank → E) :
    V.hT (∑ i, x i • V.frame i) (∑ k, y k • V.frame k) = ∑ i, ∑ k, star (x i) * V.gram i k * y k := by
  rw [map_sum V.hT, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, HSpace.gram, starRingEnd_apply]
  ring

theorem mem_hermitianStandardLattice_iff_pairing_integral (V : HSpace E) (x : V.V) : x ∈ V.L0 ↔ ∀ y ∈ V.L0, ∃ o : 𝓞 E, (o : E) = V.hT y x := by
  have h : Formalism.E.hdual V.hT V.L0 = V.L0 := V.baseLattice_isUnimodular
  conv_lhs => rw [← h]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one, LinearMap.restrictScalars_apply]

end Lattice


open GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown (offS homInt homLat latFin latFinAA mapUp mapDown locPart gramFin AEf vacSign vacSignOf theta0
  HyperspecialFixesVacuum HomLatSelfDual mapUp_add mapUp_neg mapUp_zero)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Adeles

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

open Classical in

def idemOff : Af F :=
  ⟨fun v => if v ∈ S then 0 else 1, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact zero_mem _
    · simp only [h, if_false]; exact one_mem _⟩

open Classical in
theorem evalV_idemOff (v : HeightOneSpectrum (𝓞 F)) : evalV F v (idemOff F S) = if v ∈ S then 0 else 1 := rfl

theorem idemOff_int : idemOff F S ∈ intAf F := by
  intro v
  rw [evalV_idemOff]
  split_ifs
  · exact zero_mem _
  · exact one_mem _

variable {F} in
theorem intAf_mul {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem intAf_one : (1 : Af F) ∈ intAf F := fun v => by
  rw [map_one]; exact one_mem _

variable {F} in
theorem Af_ext {a b : Af F} (h : ∀ v, evalV F v a = evalV F v b) : a = b :=
  RestrictedProduct.ext _ _ h

def liftOff : Af F →ₗ[F] AF F :=
  (LinearMap.inr F (Ainf F) (Af F)) ∘ₗ LinearMap.mulLeft F (idemOff F S)

theorem liftOff_apply (α : Af F) : liftOff F S α = pairA F 0 (idemOff F S * α) := rfl


def liftMul {E : Type} [Field E] [Algebra F E] (c : E) : Af F ⊗[F] E →+ AF F ⊗[F] E :=
  ((liftOff F S).rTensor E).toAddMonoidHom.comp (AddMonoidHom.mulLeft ((1 : Af F) ⊗ₜ[F] c))

theorem liftMul_apply {E : Type} [Field E] [Algebra F E] (c : E) (z : Af F ⊗[F] E) :
    liftMul F S c z = (liftOff F S).rTensor E (((1 : Af F) ⊗ₜ[F] c) * z) := rfl

end Adeles


theorem selfDualLattice_frame_span_integral_coordinates (V : HSp D) {x y : Fin V.rank → D.host.E} (hx : x ∈ L0c D V) (hy : y ∈ L0c D V) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = ∑ i, ∑ k, star (x i) * V.gram i k * y k := by
  obtain ⟨o, ho⟩ := (mem_hermitianStandardLattice_iff_pairing_integral V _).1 hy _ hx
  exact ⟨o, ho.trans (hT_coord V x y)⟩

def latRankOne (A B : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA A B) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, (∀ v ∈ S, evalV D.host.F v α = 0) ∧
    ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ L0c D A, ∃ y ∈ L0c D B,
      w = Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * star (x i) * y j)}



theorem rankOne_mem (A B : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {q : Fin A.rank → D.host.E}
    (hq : q ∈ L0c D A) {z : Fin B.rank → AEf D} (hz : z ∈ latFinAA B) :
    (Matrix.of fun i j => liftMul D.host.F S (star (q i)) (z j) : WA A B) ∈ latRankOne A B S := by
  let Φ : (Fin B.rank → AEf D) →+ WA A B := AddMonoidHom.mk'
    (fun z => Matrix.of fun i j => liftMul D.host.F S (star (q i)) (z j))
    fun z z' => Matrix.ext fun i j => (liftMul D.host.F S (star (q i))).map_add (z j) (z' j)
  have hle : latFinAA B ≤ (latRankOne A B S).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, u, ⟨a, ha, y, hy, rfl⟩, rfl⟩
    refine AddSubgroup.subset_closure ⟨idemOff D.host.F S * β, intAf_mul (idemOff_int _ _) hβ, fun v hv => ?_,
      a, ha, q, hq, y, hy, ?_⟩
    · rw [map_mul, evalV_idemOff, if_pos hv, zero_mul]
    · ext i j
      change liftMul D.host.F S (star (q i)) (β ⊗ₜ[D.host.F] (a * y j)) = _
      simp only [liftMul_apply, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.rTensor_tmul,
        liftOff_apply]
      congr 1
      ring
  exact hle hz


theorem unramOutside_iff (χ : (AE D)ˣ →* Circle) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Formalism.L2.Theta.UnramOutside D χ S ↔ GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown.UnramOutside D S χ := Iff.rfl

def HalfIntegral (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ u ∈ homLat V W S, ∀ u' ∈ homLat V W S, ψ (symplH V W u u') = 1



theorem hHom_smul_right (V W : HSp D) (c : AE D) (x y : WA V W) : hHom V W x (c • y) = c * hHom V W x y := by
  unfold hHom
  split_ifs
  all_goals
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring


variable {X : ThetaX D} {T : ThetaTied D X}

def FixesVacuumWhere (Wl : WeilTied D X T)
    (P : ∀ _ _ : HSp D, Finset (HeightOneSpectrum (𝓞 D.host.F)) → Prop) : Prop :=
  ∀ (V W : HSp D) (χ χ' : X.Chr), V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), P V W S →
      GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown.UnramOutside D S (T.eChr χ) → GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown.UnramOutside D S (T.eChr χ') →
      ∀ g ∈ KsphC V S, ∀ h ∈ KsphC W S, ∀ Φ : X.Sch V W, GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown.IsVacuum Wl V W S Φ →
        Wl.om V W χ χ' (g, h) Φ = Φ

def halfA (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2))




end GlobalTheory.WeilUnramifiedCompare

end
