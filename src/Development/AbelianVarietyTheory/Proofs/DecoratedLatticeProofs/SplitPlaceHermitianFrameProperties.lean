import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponenStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section

namespace GlobalTheory.UnitSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul (S : HSp D) (g g' : GA D S) : mt S (g * g') = mt S g * mt S g' := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem eq_of_parts {A : Type*} [CommRing A] {e f m m' o : A} (k1 : (e + f) * (m - o) = m - o)
    (k2 : (e + f) * (m' - o) = m' - o) (k3 : e * m = e * m') (k4 : f * m' = f * m) : m = m' := by
  linear_combination (-1 : A) * k1 + k2 + k3 - k4

theorem mt_unit (S : HSp D) (g : GA D S) :
    ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g = (HSpace.gram S).map (incA D) := g.2

theorem gram_mul_conj_inv (S : HSp D) (e : AE D) (g : GA D S) :
    (HSpace.gram S).map (incA D) * (cA D e • mt S g⁻¹) =
      ((e • mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
  have hu := mt_unit S g
  have h1 : mt S g * mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hmap : (e • mt S g).map (cA D) = cA D e • (mt S g).map (cA D) := by
    ext i j; simp [Matrix.map_apply, map_mul]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  calc (HSpace.gram S).map (incA D) * mt S g⁻¹
      = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g * mt S g⁻¹ := by rw [hu]
    _ = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
        rw [Matrix.mul_assoc _ (mt S g), h1, Matrix.mul_one]

theorem eq_of_split_part : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h →
    SuppAt e S h' → (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  intro D S e h h' _ hs hs' hee
  have hJu : IsUnit ((HSpace.gram S).map (incA D)).det := by
    have hd : ((HSpace.gram S).map (incA D)).det = incA D (HSpace.gram S).det := by
      rw [RingHom.map_det]; rfl
    rw [hd]; exact (gram_isUnit_det S).map _
  have hE : e • mt S h = e • mt S h' := by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul]; exact hee i j
  have hN : cA D e • mt S h⁻¹ = cA D e • mt S h'⁻¹ := by
    have h2 := (gram_mul_conj_inv S e h).trans
      ((congrArg (fun X : Matrix (Fin S.rank) (Fin S.rank) (AE D) => (X.map (cA D)).transpose * (HSpace.gram S).map (incA D)) hE).trans
        (gram_mul_conj_inv S e h').symm)
    have h3 := congrArg (fun X => ((HSpace.gram S).map (incA D))⁻¹ * X) h2
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul] using h3
  have a1 : mt S h⁻¹ * mt S h = 1 := by rw [← mt_mul, inv_mul_cancel, mt_one]
  have a2 : mt S h' * mt S h'⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hM : cA D e • mt S h' = cA D e • mt S h := by
    calc cA D e • mt S h' = cA D e • (mt S h' * mt S h⁻¹ * mt S h) := by
          rw [Matrix.mul_assoc, a1, Matrix.mul_one]
      _ = mt S h' * (cA D e • mt S h⁻¹) * mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = mt S h' * (cA D e • mt S h'⁻¹) * mt S h := by rw [hN]
      _ = cA D e • mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, a2, Matrix.one_mul]
  have hMM : mt S h = mt S h' := by
    ext i j
    have k1 := hs i j
    have k2 := hs' i j
    have k3 := hee i j
    have k4 : cA D e * mt S h' i j = cA D e * mt S h i j := by
      have := congrFun (congrFun hM i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at this; exact this
    simp only [Matrix.sub_apply] at k1 k2
    exact eq_of_parts k1 k2 k3 k4
  exact Subtype.ext (Units.ext hMM)

end GlobalTheory.UnitSplit

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_splitPart_agree_supportedAtSplitPlace : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h → SuppAt e S h' →
    (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  atlas_forward_decl GlobalTheory.UnitSplit.eq_of_split_part
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_splitPlaceHermitianFrame_GL_embedding : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), Continuous β.gl := by
  first | exact @GlobalTheory.FrameCont.continuous_gl | exact GlobalTheory.FrameCont.continuous_gl | (intros; apply GlobalTheory.FrameCont.continuous_gl <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameAt
variable {D : D7}

theorem mem_congGrp (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  have key : ∀ i j, (Ideal.Quotient.mk I) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  constructor
  · intro h i j
    have := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ I) => u.1 i j) h
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one] at this
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq, key]
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq, key] at this
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
    exact this

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mt_mul (g h : GA D S) : Formalism.L2.Theta.mt S (g * h) = Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S h := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one : Formalism.L2.Theta.mt S (1 : GA D S) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one]

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  have h1 := p.pr_sec (p.pr 1)
  rw [p.sec_pr, mul_one, map_one] at h1
  exact h1

theorem gl_map (β : Frame p S n) (g : GL n k) :
    (Formalism.L2.Theta.mt S (β.gl g)).map p.pr = β.b * g.val * β.b' := β.gl_mat g

theorem gl_inj (β : Frame p S n) : Function.Injective β.gl := by
  intro g g' h
  have h1 := congrArg (fun x => β.b' * (Formalism.L2.Theta.mt S x).map p.pr * β.b) h
  simp only [gl_map] at h1
  have e1 : ∀ x : Matrix n n k, β.b' * (β.b * x * β.b') * β.b = x := by
    intro x
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, β.b'b, Matrix.one_mul, Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  rw [e1, e1] at h1
  exact Units.ext h1

theorem det_at (β : Frame p S n) (g : GL n k) :
    ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  set a := (Formalism.L2.Theta.mt S (β.gl g)).det
  set c := (Formalism.L2.Theta.mt S (β.gl g⁻¹)).det
  have hee : p.e * p.e = p.e := p.split.1
  have hac : a * c = 1 := by
    simp only [a, c]
    rw [← Matrix.det_mul, ← mt_mul, ← map_mul, mul_inv_cancel, map_one, mt_one, Matrix.det_one]
  refine ⟨⟨p.e * a + (1 - p.e), p.e * c + (1 - p.e), ?_, ?_⟩, rfl, ?_⟩
  · linear_combination (2 - a - c) * hee + p.e * p.e * hac
  · linear_combination (2 - a - c) * hee + p.e * p.e * hac
  · simp only [Units.val_mk, map_add, map_mul, map_sub, map_one, pr_e p, one_mul, sub_self, add_zero]
    simp only [a]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, gl_map, Matrix.mul_assoc, Matrix.det_comm' β.bb' β.b'b, Matrix.mul_assoc, β.b'b,
      Matrix.mul_one]
end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mem_grpAt_iff (β : Frame p S n) (h : GA D S) : h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hL := (GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).1
  unfold grpAt
  rw [mem_congGrp]
  constructor
  · intro hh
    have hsupp : SuppAt p.e S h := by
      intro i j
      rw [hsum]
      exact (hL _).1 (hh i j)
    let M := (Formalism.L2.Theta.mt S h).map p.pr
    let M' := (Formalism.L2.Theta.mt S h⁻¹).map p.pr
    have hMM : M * M' = 1 := by
      simp only [M, M']
      rw [← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hM'M : M' * M = 1 := by
      simp only [M, M']
      rw [← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 : ∀ X Y : Matrix (Fin S.rank) (Fin S.rank) k,
        β.b' * X * β.b * (β.b' * Y * β.b) = β.b' * (X * Y) * β.b := by
      intro X Y
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul]
    let g : GL n k := ⟨β.b' * M * β.b, β.b' * M' * β.b, by rw [e2, hMM, Matrix.mul_one, β.b'b],
      by rw [e2, hM'M, Matrix.mul_one, β.b'b]⟩
    refine ⟨g, GlobalTheory.T.eq_of_splitPart_agree_supportedAtSplitPlace D S p.e h (β.gl g) p.split hsupp (β.gl_supp g) ?_⟩
    intro i j
    rw [← p.sec_pr, ← p.sec_pr]
    congr 1
    have := congrArg (fun X => X i j) (gl_map β g)
    simp only [Matrix.map_apply] at this
    rw [this]
    show M i j = (β.b * (β.b' * M * β.b) * β.b') i j
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨g, rfl⟩ i j
    rw [(hL _)]
    have := β.gl_supp g i j
    rw [hsum] at this
    exact this
end

theorem frame_facts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), (∀ h : GA D S, h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g) ∧ Function.Injective β.gl ∧ Continuous β.gl ∧ (∀ L : Lat S, IsSelfDualC S L → ∃ Λ : Submodule 𝒪[k] (n → k), Λ.IsLattice k ∧ β.IsLat L Λ ∧ ∀ g, InK S L (· = p.v) (β.gl g) ↔ g • Λ = Λ) ∧ (∀ (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsLattice k → ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v)) ∧ ∀ g, ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  intro D k _ _ _ _ p S n _ _ β
  exact ⟨mem_grpAt_iff β, gl_inj β, GlobalTheory.T.continuous_splitPlaceHermitianFrame_GL_embedding D k p S n β, GlobalTheory.T.selfDual_splitComponent_isLattice_stabilizer_eq D k p S n β, GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k p S n β, det_at β⟩

end GlobalTheory.FrameAt
end
end
