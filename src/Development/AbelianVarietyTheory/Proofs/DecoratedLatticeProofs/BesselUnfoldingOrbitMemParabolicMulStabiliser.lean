import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl

theorem matrix_mulVec_mem_adeleIdealSupportedOnPlaces {D : D7} {P : Pl D → Prop} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D))
    (y : Fin n → AE D) (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem matrixColumnScaledByAdele_zero {D : D7} {m n : ℕ} (x : Mx D m n) (i : Fin n) : colMul x i 0 = 0 := by
  funext k; simp [colMul]

theorem carriesLattice_wittEmbedding_iff_core : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (L₀ : GlobalTheory.FinPl.Lat S₀) (v : GlobalTheory.FinPl.Pl D) (g : GA D S₀), GlobalTheory.FinPl.MonoAt d L L₀ v → (GlobalTheory.FinPl.Moves S (d.emb0 g) L L (· = v) ↔ GlobalTheory.FinPl.Moves S₀ g L₀ L₀ (· = v)) := by
  intro D S S₀ ρ d L L₀ v g hM
  have hpX : ∀ z : Fin S₀.rank → AE D, d.pX *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
  have hpY : ∀ z : Fin S₀.rank → AE D, d.pY *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
  have hp0 : ∀ z : Fin S₀.rank → AE D, d.p0 *ᵥ (d.j0 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
  have key : ∀ z : Fin S₀.rank → AE D, d.j0 *ᵥ z ∈ latV S L (· = v) ↔ z ∈ latV S₀ L₀ (· = v) := fun z => by
    rw [hM, hpX, hpY, hp0]
    simp only [Pi.zero_apply, matrixColumnScaledByAdele_zero, zero_mem, implies_true, true_and]
  have hj : ∀ z : Fin S₀.rank → AE D, mt S (d.emb0 g) *ᵥ (d.j0 *ᵥ z) = d.j0 *ᵥ (mt S₀ g *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  constructor
  · intro h z hz
    rw [← key, ← key, ← hj]
    exact h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hz)
  · intro h y hy
    have eX : d.pX *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pX *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
    have eY : d.pY *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pY *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
    have e0 : d.p0 *ᵥ (mt S (d.emb0 g) *ᵥ y) = mt S₀ g *ᵥ (d.p0 *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding]
    rw [hM y, hM (mt S (d.emb0 g) *ᵥ y), eX, eY, e0]
    exact and_congr Iff.rfl (and_congr Iff.rfl (h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hy)))

end GlobalTheory.FinPl

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FinPl.OrbitCoset

variable {D : D7}

theorem mem_congGrp_iff' (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ (mt V g).map (Ideal.Quotient.mk I) = 1 := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

theorem matrixTransform_wittCoreEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (h : GA D S₀) :
    mt S (d.emb0 h) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ h ⬝ d.p0 + d.jY ⬝ d.pY := by
  conv_lhs => rw [← Matrix.mul_one (mt S (d.emb0 h)), ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclY]

theorem wittCoreEmbedding_mem_supportedSubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {h : GA D S₀}
    (hh : h ∈ grpAt S₀ P) : d.emb0 h ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at hh ⊢
  have hadd : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (A + B).map (Ideal.Quotient.mk (idAt D P)) =
      A.map (Ideal.Quotient.mk (idAt D P)) + B.map (Ideal.Quotient.mk (idAt D P)) :=
    fun A B => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add A B
  have key : (mt S (d.emb0 h)).map (Ideal.Quotient.mk (idAt D P)) =
      (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [matrixTransform_wittCoreEmbedding]; simp only [hadd, Matrix.map_mul, hh, Matrix.mul_one]
  rw [key, d.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem emb_mem_grpAt' {S A B : HSp D} (o : OrthDec S A B) {P : Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at ha ⊢
  have hadd : ∀ M N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (M + N).map (Ideal.Quotient.mk (idAt D P)) =
      M.map (Ideal.Quotient.mk (idAt D P)) + N.map (Ideal.Quotient.mk (idAt D P)) :=
    fun M N => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add M N
  have key : (mt S (o.emb (a, 1))).map (Ideal.Quotient.mk (idAt D P)) =
      (o.jA ⬝ o.pA + o.jB ⬝ o.pB).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [o.mt_emb, mt_one]; simp only [hadd, Matrix.map_mul, ha, Matrix.mul_one]
  rw [key, o.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem inK_mul' {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a b : GA D S} (ha : InK S L P a) (hb : InK S L P b) :
    InK S L P (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, fun y hy => ?_⟩
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [mt_mul, ← Matrix.mulVec_mulVec, ← ha.2 _ hy', hb.2 y hy]

end GlobalTheory.FinPl.OrbitCoset

namespace GlobalTheory.FinPl.OrbitCoset

theorem orbit_coset : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ) (L : Lat B.V) (L₀ : Lat B.V₀) (v : Pl D), MonoAt B.d L L₀ v →
    ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ a ∈ grpAt B.A (· = v), ∀ κ₀, InK B.V₀ L₀ (· = v) κ₀ → ∀ κ,
    InK B.V L (· = v) κ → ∃ r ∈ besGrp B.d B.o, r ∈ grpAt B.V (· = v) ∧ ∃ κ', InK B.V L (· = v) κ' ∧
      n * B.d.emb0 (B.o.emb (a, 1) * κ₀) * κ = r * κ' := by
  intro D σ B L L₀ v hM n hn hnv a ha κ₀ hκ₀ κ hκ
  refine ⟨n * embA B.d B.o a, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, rfl⟩),
    mul_mem hnv (wittCoreEmbedding_mem_supportedSubgroup B.d _ (emb_mem_grpAt' B.o ha)), B.d.emb0 κ₀ * κ,
    inK_mul' ⟨wittCoreEmbedding_mem_supportedSubgroup B.d _ hκ₀.1, (carriesLattice_wittEmbedding_iff_core D B.V B.V₀ σ B.d L L₀ v κ₀ hM).2 hκ₀.2⟩ hκ, ?_⟩
  rw [map_mul, embA_apply]
  group

end GlobalTheory.FinPl.OrbitCoset

end
end
