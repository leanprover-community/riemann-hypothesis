import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdeleGeneratesPolarisationIdealConjPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesLiftLevelDatumEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMapsIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledTensorLatticeLeCompletedHomLatticeOffPlace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NsmulMemHatA
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPEqCP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVectorDatumEqSumLevelClassIndicators

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatePlacesProductIdeal_proper_odd_coprime : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e (Pg ∪ Q) → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ ∧ GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ ∧ IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) ∧ IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) := by
  first | exact @GlobalTheory.LiftIdeal.liftI_props | exact GlobalTheory.LiftIdeal.liftI_props | (intros; apply GlobalTheory.LiftIdeal.liftI_props <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.MoverGlue

section Alg
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def glue (σ : R →+* R) (ε : R) (P Q : Matrix n n R) : Matrix n n R :=
  ε • P + σ ε • (Q.map σ)ᵀ + (1 - ε - σ ε) • (1 : Matrix n n R)

theorem glue_cT (σ : R →+* R) (hσ : ∀ z, σ (σ z) = z) (ε : R) (P Q : Matrix n n R) :
    ((glue σ ε P Q).map σ)ᵀ = σ ε • (P.map σ)ᵀ + ε • Q + (1 - ε - σ ε) • (1 : Matrix n n R) := by
  ext i j
  simp only [glue, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_mul, map_sub, map_one, hσ]
  by_cases h : i = j
  · subst h; simp <;> ring
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)] <;> ring

theorem scal_facts (σ : R →+* R) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0) :
    σ ε * σ ε = σ ε ∧ σ ε * ε = 0 ∧ ε * (1 - ε - σ ε) = 0 ∧ σ ε * (1 - ε - σ ε) = 0 ∧
      (1 - ε - σ ε) * ε = 0 ∧ (1 - ε - σ ε) * σ ε = 0 ∧ (1 - ε - σ ε) * (1 - ε - σ ε) = 1 - ε - σ ε := by
  have hσσ : σ ε * σ ε = σ ε := by rw [← map_mul, hε]
  have hσε : σ ε * ε = 0 := by rw [mul_comm, hεσ]
  have h1 : ε * (1 - ε - σ ε) = 0 := by linear_combination (-1 : R) * hε - hεσ
  have h2 : σ ε * (1 - ε - σ ε) = 0 := by linear_combination (-1 : R) * hσσ - hσε
  refine ⟨hσσ, hσε, h1, h2, by rw [mul_comm, h1], by rw [mul_comm, h2], ?_⟩
  linear_combination (1 : R) * hε + hσσ + 2 * hεσ

theorem smul_glue (σ : R →+* R) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0) (P Q : Matrix n n R) :
    ε • glue σ ε P Q = ε • P := by
  obtain ⟨-, -, h1, -⟩ := scal_facts σ ε hε hεσ
  simp only [glue, smul_add, smul_smul, hε, hεσ, h1, zero_smul, add_zero]

theorem off_smul_glue_cT (σ : R →+* R) (hσ : ∀ z, σ (σ z) = z) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0)
    (P Q : Matrix n n R) :
    (1 - ε - σ ε) • ((glue σ ε P Q).map σ)ᵀ = (1 - ε - σ ε) • (1 : Matrix n n R) := by
  obtain ⟨-, -, -, -, h3, h4, h5⟩ := scal_facts σ ε hε hεσ
  rw [glue_cT σ hσ]
  simp only [smul_add, smul_smul, h3, h4, h5, zero_smul, zero_add]

theorem glue_unitary (σ : R →+* R) (hσ : ∀ z, σ (σ z) = z) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0)
    (P Q : Matrix n n R) (hPQ : ε • (P * Q) = ε • (1 : Matrix n n R)) (hQP : ε • (Q * P) = ε • (1 : Matrix n n R)) :
    glue σ ε P Q * ((glue σ ε P Q).map σ)ᵀ = 1 ∧ ((glue σ ε P Q).map σ)ᵀ * glue σ ε P Q = 1 := by
  obtain ⟨hσσ, hσε, h1, h2, h3, h4, h5⟩ := scal_facts σ ε hε hεσ
  have hsum : ε • (1 : Matrix n n R) + σ ε • (1 : Matrix n n R) + (1 - ε - σ ε) • (1 : Matrix n n R) = 1 := by
    rw [← add_smul, ← add_smul]; simp
  have hsum' : σ ε • (1 : Matrix n n R) + ε • (1 : Matrix n n R) + (1 - ε - σ ε) • (1 : Matrix n n R) = 1 := by
    rw [add_comm (σ ε • (1 : Matrix n n R))]; exact hsum
  have key : ∀ M N : Matrix n n R, ε • (M * N) = ε • (1 : Matrix n n R) →
      σ ε • ((N.map σ)ᵀ * (M.map σ)ᵀ) = σ ε • (1 : Matrix n n R) := by
    intro M N hMN
    ext i j
    have := congrArg σ (congrFun (congrFun hMN j) i)
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul] at this
    rw [← Matrix.transpose_mul, ← Matrix.map_mul]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.map_apply, this]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  rw [glue_cT σ hσ]
  constructor
  · simp only [glue, add_mul, mul_add, smul_mul_smul_comm, hε, hεσ, hσε, hσσ, h1, h2, h3, h4, h5, zero_smul,
      add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
    rw [hPQ, key P Q hPQ]
    first | exact hsum | exact hsum'
  · simp only [glue, add_mul, mul_add, smul_mul_smul_comm, hε, hεσ, hσε, hσσ, h1, h2, h3, h4, h5, zero_smul,
      add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
    rw [hQP, key Q P hQP]
    first | exact hsum | exact hsum'

end Alg

variable {D : D7}

theorem exists_mov (S : HSp D) (k : GA D S) :
    ∃ Λ' : Lt D.host.E S.rank, IsMov (fmtC S k⁻¹) Λ' (stdL D.host.E S.rank) := by
  have hmul : ∀ g h : GA D S, fmtC S (g * h) = fmtC S g * fmtC S h := by
    intro g h
    simp only [fmtC, cM, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]
  have hone : fmtC S 1 = 1 := by
    simp only [fmtC, cM, Formalism.L2.Theta.mt, map_one, Units.val_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  let G : GL (Fin S.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    ⟨fmtC S k, fmtC S k⁻¹, by rw [← hmul, mul_inv_cancel, hone], by rw [← hmul, inv_mul_cancel, hone]⟩
  have hfg : (stdL D.host.E S.rank).FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span D.host.E ((stdL D.host.E S.rank : Set (Fin S.rank → D.host.E))) = ⊤ := by
    rw [stdL, Submodule.span_span_of_tower]
    have : (Set.range fun a : Fin S.rank => (Pi.single a (1 : D.host.E) : Fin S.rank → D.host.E)) =
        Set.range (Pi.basisFun D.host.E (Fin S.rank)) := by
      ext v; simp [Pi.basisFun_apply]
    rw [this, (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
  obtain ⟨Λ, -, -, -, hΛ⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E S.rank _ G hfg hsp
  refine ⟨Λ, fun u => ?_⟩
  have hV : ∀ L : Lt D.host.E S.rank, ((hatV L : AddSubgroup _) : Set (Fin S.rank → AfE D)) =
      (GlobalTheory.AdLat.hat D.host.F (L : Set (Fin S.rank → D.host.E)) : Set _) := fun L => rfl
  have hGi : ∀ z, fmtC S k⁻¹ *ᵥ (fmtC S k *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec]
  constructor
  · intro hu
    refine ⟨fmtC S k *ᵥ u, ?_, (hGi u).symm⟩
    have : fmtC S k *ᵥ u ∈ ((hatV Λ : AddSubgroup _) : Set (Fin S.rank → AfE D)) := by
      rw [hV, hΛ]; exact ⟨u, hu, rfl⟩
    exact this
  · rintro ⟨u₀, hu₀, rfl⟩
    have : u₀ ∈ ((hatV Λ : AddSubgroup _) : Set (Fin S.rank → AfE D)) := hu₀
    rw [hV, hΛ] at this
    obtain ⟨w, hw, rfl⟩ := this
    change fmtC S k⁻¹ *ᵥ (fmtC S k *ᵥ w) ∈ hatV (stdL D.host.E S.rank)
    rw [hGi]; exact hw

theorem map_smul_ringHom {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {m p : Type} (c : R) (M : Matrix m p R) :
    (c • M).map f = f c • M.map f := by
  ext i j; simp [map_mul]

end GlobalTheory.MoverGlue

open GlobalTheory.MoverGlue in

theorem GlobalTheory.LiftLevel.exists_mover : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ a : AE D, (∃ b : AE D, a * b = e) → ∃ (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) := by
  intro D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a hab
  obtain ⟨b, hab⟩ := hab
  have he2 : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  let φ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* EAf D :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom
  let ψ : EAf D →+* (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm.toAlgHom.toRingHom
  have hφψ : ∀ z, φ (ψ z) = z := fun z => AlgEquiv.apply_symm_apply _ z
  have htoE : ∀ z : AE D, toEAf D z = φ (finPart D z) := fun z => rfl
  let σ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* (Af D.host.F ⊗[D.host.F] D.host.E) :=
    sigR (Af D.host.F) D.sp.cm.sig
  have hσ : ∀ z, σ (σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      show (Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) ((Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) (x ⊗ₜ y)) = x ⊗ₜ y
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact star_star y
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hfc : ∀ z : AE D, finPart D (cA D z) = σ (finPart D z) := fun z =>
    GlobalTheory.UnitaryGlue.map_sigR (sndA D.host.F) D.sp.cm.sig z
  set ε := finPart D e with hεdef
  have hεε : ε * ε = ε := by rw [← map_mul, he2]
  have hεσ : ε * σ ε = 0 := by rw [← hfc, ← map_mul, hec, map_zero]
  let Bs : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := βS.val.map ψ
  let Bi : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (βS⁻¹).val.map ψ
  have hBB : Bs * Bi = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB' : Bi * Bs = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  let P := finPart D a • Bs
  let Qm := finPart D b • Bi
  have hPQ : ε • (P * Qm) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    rw [smul_mul_smul_comm, hBB, smul_smul, ← map_mul, ← map_mul, hab, he2]
  have hQP : ε • (Qm * P) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    rw [smul_mul_smul_comm, hBB', smul_smul, ← map_mul, ← map_mul, mul_comm b a, hab, he2]
  obtain ⟨hu1, hu2⟩ := glue_unitary σ hσ ε hεε hεσ P Qm hPQ hQP
  set hf := glue σ ε P Qm with hhf
  let gfGL : GL (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨hf, (hf.map σ)ᵀ, hu1, hu2⟩
  have hJ : JR (F := D.host.F) (Af D.host.F) (HSpace.gram S) = 1 := by
    rw [C.m.gS]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hmem : gfGL ∈ HR (Af D.host.F) D.sp.cm.sig (HSpace.gram S) := by
    show Formalism.UG.cT σ hf * JR (F := D.host.F) (Af D.host.F) (HSpace.gram S) * hf = JR (F := D.host.F) (Af D.host.F) (HSpace.gram S)
    rw [hJ, Matrix.mul_one]; exact hu2
  obtain ⟨g, hgC, hgf⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D S).1 gfGL hmem
  obtain ⟨Λ', hΛ'⟩ := exists_mov S g

  have hmt1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
  have hact : ∀ x : WO S T, actO S T g 1 x = HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹) := by
    intro x; show HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T 1) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (Formalism.L2.Theta.mt S g⁻¹) = _; rw [hmt1, Matrix.one_mul]
  have hKf : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = (hf.map σ)ᵀ := by
    have h1 : ((finHom S g⁻¹).val) = (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) := rfl
    rw [← h1, map_inv, hgf]; rfl
  have hKi : (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) = 1 := by
    have h1 : ((infHom S g⁻¹).val) = (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) := rfl
    have hg1 : infHom S g = 1 := hgC
    rw [← h1, map_inv, hg1, inv_one, Units.val_one]
  refine ⟨g, Λ', ⟨hgC, ?_, ?_⟩, hΛ'⟩
  · intro x hx
    rw [hact]
    have hX : (1 - ε - σ ε) • x.map (finPart D) = x.map (finPart D) := by
      ext i j
      have := congrArg (finPart D) (hx i j)
      rw [map_mul, map_sub, map_sub, map_one, hfc] at this
      simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] using this
    ext i j
    refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · have h := congrFun (congrFun (show (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (infPart D) = x.map (infPart D) by
        rw [Matrix.map_mul, hKi, Matrix.mul_one]) i) j
      simpa only [Matrix.map_apply] using h
    · have h := congrFun (congrFun (show (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (finPart D) = x.map (finPart D) by
        rw [Matrix.map_mul, hKf]
        conv_lhs => rw [← hX]
        rw [Matrix.smul_mul, ← Matrix.mul_smul, off_smul_glue_cT σ hσ ε hεε hεσ, Matrix.mul_smul, Matrix.mul_one, hX]) i) j
      simpa only [Matrix.map_apply] using h
  · intro x hx
    rw [hact]
    have hcK : ((Formalism.L2.Theta.mt S g⁻¹).map (cA D))ᵀ.map (toEAf D) = hf.map φ := by
      ext i j
      have hk := congrFun (congrFun hKf j) i
      simp only [Matrix.map_apply, Matrix.transpose_apply] at hk ⊢
      rw [htoE, hfc, hk, hσ]
    have hεhf : (toEAf D e) • hf.map φ = (toEAf D e * toEAf D a) • βS.val := by
      have h1 : ε • hf = ε • P := smul_glue σ ε hεε hεσ P Qm
      ext i j
      have h2 := congrFun (congrFun h1 i) j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at h2 ⊢
      rw [htoE, htoE, ← map_mul, h2]
      simp only [P, Bs, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hφψ, hεdef, mul_assoc]
    set Z := (HMul.hMul ((x.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) ((HSpace.gram T).map (incA D))).map (toEAf D) with hZdef
    have hxc : e • (x.map (cA D))ᵀ = (x.map (cA D))ᵀ := by
      ext i j
      have := congrArg (cA D) (hx j i)
      rw [map_mul, GlobalTheory.DualPairCheck.cA_cA] at this
      simpa only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul] using this
    have hZ : toEAf D e • Z = Z := by
      rw [hZdef]
      conv_rhs => rw [← hxc]
      rw [Matrix.smul_mul, GlobalTheory.MoverGlue.map_smul_ringHom]
    have hL2 : (HMul.hMul (((HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) ((HSpace.gram T).map (incA D))).map (toEAf D) =
        HMul.hMul (hf.map φ) Z := by
      have h3 : (((HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (cA D))ᵀ :
          Matrix (Fin S.rank) (Fin T.rank) (AE D)) = HMul.hMul ((Formalism.L2.Theta.mt S g⁻¹).map (cA D))ᵀ
          ((x.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) := by
        rw [Matrix.map_mul, Matrix.transpose_mul]
      rw [h3, Matrix.mul_assoc, Matrix.map_mul, hcK]
    have hLHS : HMul.hMul (HMul.hMul (βS⁻¹).val (HMul.hMul (hf.map φ) Z)) βT.val = (toEAf D e * toEAf D a) • HMul.hMul Z βT.val := by
      conv_lhs => rw [← hZ]
      rw [Matrix.mul_smul, ← Matrix.smul_mul, hεhf, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hRHS : toEAf D a • HMul.hMul βS.val (HMul.hMul (HMul.hMul (βS⁻¹).val Z) βT.val) = (toEAf D e * toEAf D a) • HMul.hMul Z βT.val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      conv_lhs => rw [← hZ]
      rw [Matrix.smul_mul, smul_smul, mul_comm (toEAf D a)]
    unfold GlobalTheory.LiftLevel.adjA frMapAdj
    have hGS : (HSpace.gram S)⁻¹.map (incA D) = 1 := by
      rw [C.m.gS]; simp
    rw [hGS]
    simp only [Matrix.one_mul]
    rw [hL2, hLHS, ← hRHS]
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_unitary_mover_standard_lattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ a : AE D, (∃ b : AE D, a * b = e) → ∃ (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) := by
  atlas_forward_decl GlobalTheory.LiftLevel.exists_mover
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem isLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsLattice E (stdL E n) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  refine Submodule.subset_span ?_
  exact Submodule.subset_span ⟨a, by simp⟩

theorem liftL_nsmul_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO (S := S) (T := T)
    (ΛS := stdL D.host.E S.rank) (ΛT := ΛT) (isLattice_stdL D.host.E S.rank) hΛT.1
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  refine ⟨k₄ * k₂, Nat.mul_pos hk₄ hk₂, fun x hx => ?_⟩
  obtain ⟨hhalf, hint, -⟩ := hx
  have hx0 : (k₂ • x).map (infPart D) = 0 := by
    ext i j
    show infPart D ((k₂ • x) i j) = 0
    rw [Matrix.smul_apply, ← hhalf i j, nsmul_eq_mul, RingHom.map_mul, RingHom.map_mul, hinf, zero_mul, mul_zero]
  rw [mul_smul]
  exact h₄ (k₂ • x) hx0 (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₂ x hint)

end GlobalTheory.LiftLevel
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  atlas_forward_decl GlobalTheory.LiftLevel.liftL_nsmul_mem_latO
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftMul

variable {D : D7}

theorem exists_den_AA (D : D7) :
    ∃ d : ℕ, 0 < d ∧ ∀ a ∈ D.host.AA, ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E) := by
  obtain ⟨b, hb, hbI⟩ := D.host.AA.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero ?_, fun a ha => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    obtain ⟨o, ho⟩ := hbI a ha
    refine ⟨c * o, ?_⟩
    show _ = algebraMap (𝓞 D.host.E) D.host.E (c * o)
    rw [map_mul, ho, Algebra.smul_def, ← mul_assoc, ← map_mul, hc, map_natCast]

def fA (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    WO S T →+ Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)

theorem gen_int (S T : HSp D) (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank)) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    {d : ℕ} {α : Af D.host.F} (hα : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {a : D.host.E} (ha : ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E))
    {s : Fin S.rank → D.host.E} (hs : s ∈ stdL D.host.E S.rank) {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) :
    IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) := by
  obtain ⟨o, ho⟩ := ha
  have hc : toEAf D (incA D (d : D.host.E) * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [← map_mul, ho]
    exact GlobalTheory.IdemIntegral.eToEAf_int D o
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.ConjHalfInt.map_gen, GlobalTheory.ConjHalfInt.adj_shape, Matrix.mul_smul, Matrix.smul_mul]
  refine GlobalTheory.ConjHalfInt.isIntM_smul (GlobalTheory.PlaceVec.cF_mem_int (mul_mem hc hα)) ?_
  have hA : (S.gram⁻¹).map (eToEAf D) *
      ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      Matrix.of fun m (_ : Fin 1) => eToEAf D (s m) := by
    ext m z
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
      GlobalTheory.ConjHalfInt.cF_eToEAf, ← map_mul, ← map_sum]
    rw [GlobalTheory.ConjHalfInt.gram_inv_star]
  have hB : ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D) =
      Matrix.of fun (_ : Fin 1) m => eToEAf D (∑ l, star (t l) * T.gram l m) := by
    ext z m
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
      GlobalTheory.ConjHalfInt.cF_eToEAf, ← map_mul, ← map_sum]
  have e : (βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) *
      (((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ *
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ) *
      (T.gram.map (eToEAf D) * βT.val) =
      ((βS⁻¹).val * ((S.gram⁻¹).map (eToEAf D) *
        ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ)) *
      ((((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D)) *
        βT.val) := by
    simp only [Matrix.mul_assoc]
  rw [e, hA, hB]
  exact GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int hβS hs)
    (GlobalTheory.ConjHalfInt.pair_row_int hsd hβT ht)

theorem lat_int (S T : HSp D) (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank)) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    {d : ℕ} (hd : ∀ a ∈ D.host.AA, ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E))
    {x : WO S T}
    (hx : x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) :
    IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • x)) := by
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • u)))
    ?_ ?_ ?_ ?_ hx
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      exact gen_int S T ΛT hsd βS βT hβS hβT hα' (hd a ha) hs ht
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
    exact fun i j => neg_mem (hu i j)

theorem red_nsmul {b a : ℕ} (PP : Formalism.L2.DIV.Pl D.host.E) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N)
    {m : ℕ} (hm : (m : 𝓞 D.host.E) ∈ PP.asIdeal) : IsIntM (m • N) ∧ redM PP (m • N) = 0 := by
  have hI : IsIntM (m • N) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul]; exact mul_mem (natCast_mem _ m) (hN i j)
  refine ⟨hI, ?_⟩
  ext i j
  simp only [redM, dif_pos (hI i j), Matrix.zero_apply]
  have e : (⟨(m • N) i j, hI i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (m : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨N i j, hN i j⟩ := by
    apply Subtype.ext; simp [Matrix.smul_apply, nsmul_eq_mul]
  rw [e, map_mul, map_natCast]
  have h0 : (m : Formalism.L2.DIV.kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal) m]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  rw [h0, zero_mul]

theorem nsmul_mem_liftL : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hne h2 e hidem
  obtain ⟨d, hd0, hd⟩ := exists_den_AA D
  set m2 : ℕ := ∏ PP ∈ Pg ∪ Q, Ideal.absNorm PP.asIdeal with hm2
  have hm2pos : 0 < m2 := Finset.prod_pos fun PP _ =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)
  have hm2mem : ∀ PP ∈ Pg ∪ Q, (m2 : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP => by
    rw [hm2, Nat.cast_prod]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hPP) (Ideal.absNorm_mem _)
  refine ⟨d * m2, Nat.mul_pos hd0 hm2pos, fun x hx hh => ?_⟩
  have hint := lat_int S T ΛT hsd βS βT hβS hβT hd hx
  have heq : frMapAdj S T βS βT ((d * m2) • x) = m2 • frMapAdj S T βS βT (incA D (d : D.host.E) • x) := by
    have hdx : d • x = incA D (d : D.host.E) • x := by rw [map_natCast, Nat.cast_smul_eq_nsmul]
    rw [mul_comm d m2, ← smul_smul, hdx]
    exact (fA S T βS βT).map_nsmul _ _
  show IsHalf (cA D e) ((d * m2) • x) ∧ IsIntM (frMapAdj S T βS βT ((d * m2) • x)) ∧
    ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT ((d * m2) • x)) = 0
  refine ⟨fun i j => ?_, ?_, fun PP hPP => ?_⟩
  · rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hh i j]
  · obtain ⟨PP, hPP⟩ := hne
    rw [heq]; exact (red_nsmul PP hint (hm2mem PP (Finset.mem_union_left _ hPP))).1
  · rw [heq]; exact (red_nsmul PP hint (hm2mem PP hPP)).2

end GlobalTheory.LiftMul

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nsmul_mem_lift_points_of_completed_hom_lattice_half : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  atlas_forward_decl GlobalTheory.LiftMul.nsmul_mem_liftL
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shiftedTensorLatticePart_mem_liftLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  first | exact @GlobalTheory.LiftLevel.partAt_mem_liftL | exact GlobalTheory.LiftLevel.partAt_mem_liftL | (intros; apply GlobalTheory.LiftLevel.partAt_mem_liftL <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel.PairTriv

variable {D : D7}

theorem partAt_eq_smul {S T : HSp D} (a : AE D) (w : WO S T) : GlobalTheory.LiftLevel.partAt a w = a • w := by
  ext i j
  rfl

theorem hatA_tens_mono {S T : HSp D} (Λ : Lt D.host.E S.rank) {L L' : Lt D.host.E T.rank} (h : L ≤ L') :
    hatA S T (tens Λ L) ≤ hatA S T (tens Λ L') := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, y, hy, rfl⟩
  refine ⟨α, hα, y, ?_, rfl⟩
  refine (AddSubgroup.closure_mono ?_) hy
  rintro z ⟨v, hv, u, hu, rfl⟩
  exact ⟨v, hv, u, h hu, rfl⟩

theorem actO_back {S T : HSp D} (k : GA D S) (x : WO S T) : actO S T k 1 (actO S T k⁻¹ 1 x) = x := by
  have := GlobalTheory.WeilVacMove.actO_inv_actO (S := S) (T := T) k⁻¹ (1 : GA D T) x
  simpa using this

theorem pair_trivial : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), ∀ t ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1 := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg hodd e he a k₀ Λ' hab hmov hgen hmv Lv hLv u hu t ht
  have hsd : SelfD C.X (Lv.sh C.X.Λ) :=
    GlobalTheory.SW.Lev.selfD_idq Lv.ne_bot Lv.proper Lv.cop (GlobalTheory.SW.Lev.selfD_of_sympl C.sympl)
  have hV := GlobalTheory.SW.Base.stdL_mem_Vset (E := D.host.E) S.rank 1

  have hw : actO S T k₀⁻¹ 1 u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) :=
    (GlobalTheory.TensLatMove.mem_hatA_iff S T C.m.gS k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hmv
      (GlobalTheory.OneMapRef.Term.isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩

  obtain ⟨ht1, ht2, ht3⟩ := ht
  have hh0 : IsHalf (cA D e) (actO S T k₀⁻¹ 1 t) := GlobalTheory.WeilVacMove.isHalf_actO _ _ _ ht1
  have hfr := hmov.2.2 _ hh0
  rw [actO_back] at hfr
  have ht0 : actO S T k₀⁻¹ 1 t ∈ hatA S T (tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ)) :=
    ((hgen _ hh0).2).1 ⟨hfr ▸ ht2, fun PP hPP => hfr ▸ ht3 PP hPP⟩
  rw [← hLv] at ht0
  have ht0' := hatA_tens_mono (stdL D.host.E S.rank) (GlobalTheory.SW.Lev.smul_le_idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ) ht0
  have hF := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  set t₀ := actO S T k₀⁻¹ 1 t with ht₀
  set w := actO S T k₀⁻¹ 1 u with hw₀
  have et : t = actO S T k₀ 1 t₀ := (actO_back k₀ t).symm
  have eu : GlobalTheory.LiftLevel.partAt e u = actO S T k₀ 1 (e • w) := by
    rw [partAt_eq_smul, GlobalTheory.OneMapRef.Term.actO_smul, actO_back]
  have hhalf : cA D e • t₀ = t₀ := by
    ext i j
    exact hh0 i j
  have key : symplO S T t (GlobalTheory.LiftLevel.partAt e u) = symplO S T t₀ w := by
    rw [et, eu, hF.2.2.2.2.2.2.1, (hF.2.2.2.2.2.1 t₀ (e • w) 0).2, GlobalTheory.SplitScalar.symplO_smul, hhalf,
      ← (hF.2.2.2.2.2.1 t₀ w 0).2]
  rw [key]
  exact GlobalTheory.OneMapRef.Term.char_hatA C hV hsd t₀ ht0' w hw

end GlobalTheory.LiftLevel.PairTriv
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftGroupPoints_pair_trivial_shiftedTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), ∀ t ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1 := by
  atlas_forward_decl GlobalTheory.LiftLevel.PairTriv.pair_trivial
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledTensorLattice_le_completedHomLattice_offPlaces : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.LiftLevel.partAt_off_mem_latO | exact GlobalTheory.LiftLevel.partAt_off_mem_latO | (intros; apply GlobalTheory.LiftLevel.partAt_off_mem_latO <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.OffIdemLat

open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen

variable {D : D7}

abbrev conjProd (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) : Ideal (𝓞 D.host.E) := ∏ PP ∈ SS, conjI PP.asIdeal

theorem cP_mem_of_le {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (h : conjProd SS ≤ Q.asIdeal) : cP Q ∈ SS := by
  obtain ⟨PP, hPP, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have : PP = cP Q := eq_of_le fun x hx => by
    rw [mem_cP]
    exact hle (Ideal.subset_span ⟨x, hx, rfl⟩)
  exact this ▸ hPP

theorem conjProd_ne_bot (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) : conjProd SS ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  refine Finset.prod_ne_zero_iff.2 fun PP _ => ?_
  rw [Ne, Ideal.zero_eq_bot, GlobalTheory.LiftIdeal.conjI_eq_map,
    Ideal.map_eq_bot_iff_of_injective (f := (GlobalTheory.LiftIdeal.conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))
      (GlobalTheory.LiftIdeal.conjO D).injective]
  exact PP.ne_bot

end GlobalTheory.OffIdemLat

namespace GlobalTheory.OffIdemLat
open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen
variable {D : D7}

theorem finPart_mul_mem (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e SS) (x : D.host.E)
    (hx : ∀ j ∈ conjProd SS, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (j : D.host.E)) :
    finPart D ((1 - e - cA D e) * incA D x) ∈ intAE D := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  have hd : ∀ P ∈ SS, IsDelta Φ P (es P) := fun P hP => delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P)) := fun P hP => delta_conj hΦ (hd P hP)
  have hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q := fun Q => map_sum (evQ Φ Q) _ _
  have hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q := fun Q => by
    rw [map_sum]; exact map_sum (evQ Φ Q) _ _
  have hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q =
      1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q := fun Q => by
    change evQ Φ Q _ = _
    rw [map_sub, map_sub, map_one]; rfl
  have hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0 := fun Q => by
    rw [← ev_mul, horth, ev_zero]
  rw [hΦ.int]
  intro Q
  rw [ev_mul, hΦ.inc]
  by_cases hQ : Q ∈ SS ∨ cP Q ∈ SS
  · have h0 : Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0 := by
      rw [hO]
      rcases hQ with hQ | hQ
      · have h1 : Φ (∑ P ∈ SS, es P) Q = 1 := by
          rw [hE, Finset.sum_eq_single Q (fun P hP hne => (hd P hP).2.2 Q (Ne.symm hne))
            (fun h => absurd hQ h), (hd Q hQ).2.1]
        have h2 := hprod Q
        rw [h1, one_mul] at h2
        rw [h1, h2, sub_self, sub_zero]
      · have h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1 := by
          rw [hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by
              rw [h, cP_cP])))
            (fun h => absurd hQ h)]
          have := (hdc (cP Q) hQ).2.1
          rwa [cP_cP] at this
        have h2 := hprod Q
        rw [h1, mul_one] at h2
        rw [h1, h2, sub_zero, sub_self]
    rw [h0, zero_mul]
    exact (Q.adicCompletionIntegers D.host.E).zero_mem
  · push_neg at hQ
    refine mul_mem ?_ ?_
    · rw [hO, hE, hC]
      exact sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem
        (sum_mem fun P hP => delta_mem (hd P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)
    · have hnle : ¬ conjProd SS ≤ Q.asIdeal := fun h => hQ.2 (cP_mem_of_le h)
      obtain ⟨j, hj, hjQ⟩ := Set.not_subset.1 hnle
      obtain ⟨o, ho⟩ := hx j hj
      have hj0 : j ≠ 0 := fun h => hjQ (h ▸ zero_mem _)
      have hj0' : ((j : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hj0 (RingOfIntegers.ext (h.trans rfl))
      have hxe : x = (o : D.host.E) * ((j : D.host.E))⁻¹ := by
        rw [ho, mul_assoc, mul_inv_cancel₀ hj0', mul_one]
      have hinv := (inv_mem_iff Q hj0).2 hjQ
      have ho' : algebraMap D.host.E (Q.adicCompletion D.host.E) (o : D.host.E) ∈
          Q.adicCompletionIntegers D.host.E := HeightOneSpectrum.coe_mem_adicCompletionIntegers Q o
      change algebraMap D.host.E (Q.adicCompletion D.host.E) x ∈ Q.adicCompletionIntegers D.host.E
      rw [hxe, map_mul]
      exact mul_mem ho' hinv

end GlobalTheory.OffIdemLat

namespace GlobalTheory.OffIdemLat
open GlobalTheory.IdemSupport
variable {D : D7}

theorem fin_smul_mem {S T : HSp D} {J : Ideal (𝓞 D.host.E)} {M N : Lt D.host.E T.rank} (hMN : J • M ≤ N)
    {j : 𝓞 D.host.E} (hj : j ∈ J) {u : WO S T} (hu : u ∈ hatA S T (tens (stdL D.host.E S.rank) M)) :
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((j : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈
      hatA S T (tens (stdL D.host.E S.rank) N) := by
  refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => (pairA D.host.F 0 1 ⊗ₜ[D.host.F]
      ((j : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N)) ?_ ?_ ?_ ?_ hu
  · intro α hα y hy
    rw [GlobalTheory.LatVac.tmul_smul_finTens, one_mul, ← Matrix.transpose_smul]
    exact GlobalTheory.Ker.SignVac.finTens_mem hα
      (GlobalTheory.LiftLevel.smul_mem_tens _ (fun v hv => hMN (Submodule.smul_mem_smul hj hv)) hy)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem partAt_off_mem : ∀ (D : D7) (S T : HSp D) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (M N : Lt D.host.E T.rank), (∏ PP ∈ SS, conjI PP.asIdeal) • M ≤ N → ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) M), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ hatA S T (tens (stdL D.host.E S.rank) N) := by
  intro D S T e SS he M N hMN u hu
  have hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens (stdL D.host.E S.rank) N,
      (o : D.host.E) • y ∈ tens (stdL D.host.E S.rank) N :=
    fun o y hy => GlobalTheory.LiftLevel.smul_mem_tens o (fun v hv => Submodule.smul_mem _ o hv) hy
  have hJ : ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (conjProd_ne_bot SS)
  have h1 : (1 : D.host.E) ∈ ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
    rw [mul_inv_cancel₀ hJ]
    exact FractionalIdeal.one_mem_one _
  have key : ((1 - e - cA D e) * incA D 1) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N) := by
    refine FractionalIdeal.mul_induction_on (C := fun z => ((1 - e - cA D e) * incA D z) • u ∈
      hatA S T (tens (stdL D.host.E S.rank) N)) h1 ?_ ?_
    · intro i hi x hx
      obtain ⟨i', hi', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
      have hxJ : ∀ j ∈ conjProd SS, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (j : D.host.E) := by
        intro j hj
        obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hJ).1 hx
          (algebraMap (𝓞 D.host.E) D.host.E j) ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩))
        exact ⟨o, ho⟩
      have hint := finPart_mul_mem e SS he x hxJ
      have e1 : ((1 - e - cA D e) * incA D (algebraMap (𝓞 D.host.E) D.host.E i' * x)) • u =
          ((1 - e - cA D e) * incA D x) •
            (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) • u := by
        have e2 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) =
            incA D ((i' : 𝓞 D.host.E) : D.host.E) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) := by
          change _ = ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E)) * _
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [e2, mul_smul (incA D ((i' : 𝓞 D.host.E) : D.host.E)), GlobalTheory.Ker.SignVac.one_smul_hatA hu, smul_smul,
          mul_assoc, ← map_mul, mul_comm x]
      rw [e1]
      exact GlobalTheory.LiftLevel.smul_mem_hatA_of_int hA hint (fin_smul_mem hMN hi' hu)
    · intro x y hx hy
      rw [map_add, mul_add, add_smul]
      exact add_mem hx hy
  rw [map_one, mul_one] at key
  rw [GlobalTheory.LiftLevel.partAt_eq_smul]
  exact key

end GlobalTheory.OffIdemLat
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offIdempotent_scale_mem_completedTensorLattice : ∀ (D : D7) (S T : HSp D) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (M N : Lt D.host.E T.rank), (∏ PP ∈ SS, conjI PP.asIdeal) • M ≤ N → ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) M), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ hatA S T (tens (stdL D.host.E S.rank) N) := by
  atlas_forward_decl GlobalTheory.OffIdemLat.partAt_off_mem
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LiftLevel

theorem partAt_finW_mem_hatA_sh : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) (conjI Lv.𝔪 • C.X.Λ), GlobalTheory.LiftLevel.partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
  intro D S T C Pg Q e he Lv hLv y hy

  have hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 Lv.cop
  have h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪 := by rw [hm]; exact Submodule.mem_top
  obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1
  have hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal := by
    intro PP hPP x hx
    have h2 := mem_of_mem_conjI hx
    rw [hLv, liftI] at h2
    have h3 : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
      hPP (Ideal.prod_le_inf h2)
    have h4 := mem_of_mem_conjI h3
    have h5 : stO (stO x) = x := RingOfIntegers.ext (star_star _)
    rwa [h5] at h4
  have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
    intro PP hPP htm
    have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
  have hPQ : (Pg ∪ Q).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply Lv.proper
    rw [hLv, liftI, hne, Finset.prod_empty, Ideal.one_eq_top]
  have ht0 : (t : D.host.E) ≠ 0 := by
    obtain ⟨PP, hPP⟩ := hPQ
    intro h
    apply htP PP hPP
    have : t = 0 := RingOfIntegers.ext (h.trans rfl)
    rw [this]; exact zero_mem _

  have hsub : conjI Lv.𝔪 • C.X.Λ ≤ C.X.Λ := Submodule.smul_le_right
  have htL : ∀ v ∈ conjI Lv.𝔪 • C.X.Λ, t • v ∈ Lv.sh C.X.Λ := by
    intro v hv s hs
    have hv' : t • v ∈ Lv.𝔪 • C.X.Λ := Submodule.smul_mem_smul ht (hsub hv)
    exact Submodule.smul_mem _ s hv'
  have hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) := smul_mem_tens t htL hy
  have h0 : finW S T ((t : D.host.E) • y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
    rw [GlobalTheory.Ker.SignVac.finW_eq]
    exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hty

  have hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D :=
    GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP
  have hA' : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ),
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) :=
    fun o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y) := by
    have e2 : finW S T ((t : D.host.E) • y) =
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul,
        Matrix.transpose_smul]
    have e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]
    rw [e2, smul_smul, mul_assoc]
    have e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) =
        pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]
    rw [e4, mul_smul, ← e3, partAt_eq_smul]
  rw [e1]
  exact smul_mem_hatA_of_int hA' hz1 h0

end GlobalTheory.LiftLevel

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentPart_finitePoint_mem_shiftedTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) (conjI Lv.𝔪 • C.X.Λ), GlobalTheory.LiftLevel.partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
  atlas_forward_decl GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LiftLevel.MovedClass

open GlobalTheory.LiftLevel

variable {D : D7}

theorem partAt_eq_smul {S T : HSp D} (c : AE D) (w : WO S T) : partAt c w = c • w := by
  ext i j; rfl

theorem actO_smul' (S T : HSp D) (g : GA D S) (h : GA D T) (c : AE D) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

theorem actO_actO_inv (S T : HSp D) (g : GA D S) (x : WO S T) : actO S T g 1 (actO S T g⁻¹ 1 x) = x := by
  simpa using GlobalTheory.WeilVacMove.actO_inv_actO (S := S) (T := T) g⁻¹ 1 x

theorem finW_two (S T : HSp D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (2 • y) = 2 • finW S T y := by
  ext a k
  simp only [finW, two_nsmul, Matrix.add_apply, Matrix.of_apply, TensorProduct.tmul_add]

theorem tens_mono {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) {L L' : Lt E r} (h : L ≤ L') :
    tens Λ L ≤ tens Λ L' :=
  AddSubgroup.closure_mono fun _ ⟨v, hv, u, hu, e⟩ => ⟨v, hv, u, h hu, e⟩

theorem tens_two {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (N : Lt E r)
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ (Ideal.span {(2 : 𝓞 E)} • N)) :
    ∃ y' ∈ tens Λ N, y = 2 • y' := by
  have key : tens Λ (Ideal.span {(2 : 𝓞 E)} • N) ≤
      (tens Λ N).map (DistribMulAction.toAddMonoidHom (Matrix (Fin n) (Fin r) E) (2 : ℕ)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    rw [Submodule.ideal_span_singleton_smul] at hu
    obtain ⟨u', hu', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hu
    refine ⟨vecMulVec v u', AddSubgroup.subset_closure ⟨v, hv, u', hu', rfl⟩, ?_⟩
    ext i j
    simp [vecMulVec_apply, two_smul, two_nsmul, mul_add]
  obtain ⟨y', hy', e⟩ := key hy
  exact ⟨y', hy', e.symm⟩

theorem mem_sh {S T : HSp D} (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) :
    Lv.𝔪 • (conjI Lv.𝔪 • C.X.Λ) ≤ Lv.sh C.X.Λ := by
  intro v hv b hb
  exact Submodule.smul_mono le_rfl Submodule.smul_le_right (Submodule.smul_mem _ b hv)

theorem moved_class : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1 := by
  intro D S T C hn ΛT hT hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' hab hmov hgen hΛ' Lv hLv y hy
  rw [Submodule.mul_smul] at hy
  obtain ⟨y', hy', rfl⟩ := tens_two _ _ hy
  have hS := C.m.gS
  set std := stdL D.host.E S.rank with hstd
  set x := finW S T y' with hx
  set X := actO S T k₀ 1 x with hX
  have hX2 : actO S T k₀ 1 (finW S T (2 • y')) = 2 • X := by
    rw [finW_two, GlobalTheory.WeilVacMove.actO_two_nsmul]
  rw [hX2]

  have hxM : x ∈ hatA S T (tens std (conjI Lv.𝔪 • C.X.Λ)) := by
    rw [hx, GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.TensLatMove.intAf_one (D := D)) hy'
  have hE : partAt e x ∈ hatA S T (tens std (Lv.sh C.X.Λ)) := GlobalTheory.T.idempotentPart_finitePoint_mem_shiftedTensorLattice D S T C Pg Q e he Lv hLv y' hy'
  have hF : partAt (1 - e - cA D e) x ∈ hatA S T (tens std (Lv.sh C.X.Λ)) := by
    refine GlobalTheory.T.offIdempotent_scale_mem_completedTensorLattice D S T e (Pg ∪ Q) he _ _ ?_ x hxM
    have : (∏ PP ∈ Pg ∪ Q, conjI PP.asIdeal) = Lv.𝔪 := by rw [hLv]; rfl
    rw [this]; exact mem_sh C Lv
  have hB : (1 - cA D e) • x ∈ hatA S T (tens std (Lv.sh C.X.Λ)) := by
    have : (1 - cA D e) • x = partAt e x + partAt (1 - e - cA D e) x := by
      rw [partAt_eq_smul, partAt_eq_smul, ← add_smul]; congr 1; ring
    rw [this]; exact add_mem hE hF
  have hmov1 : IsMov (fmt T 1) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) := by
    have hmt1 : Formalism.L2.Theta.mt T 1 = 1 := by simp [Formalism.L2.Theta.mt]
    have hfmt1 : fmt T 1 = 1 := by simp [fmt, hmt1]
    rw [hfmt1]
    intro u
    exact ⟨fun h => ⟨u, h, (Matrix.one_mulVec u).symm⟩, fun ⟨u₀, h, e⟩ => by rw [e, Matrix.one_mulVec]; exact h⟩
  obtain ⟨u₀, hu₀, hu₀e⟩ := (GlobalTheory.TensLatMove.mem_hatA_iff S T hS k₀⁻¹ 1 Λ' std (Lv.sh C.X.Λ) (Lv.sh C.X.Λ)
    hΛ' hmov1 _).1 hB
  have hv : partAt (1 - cA D e) X = u₀ := by
    rw [partAt_eq_smul, hX, ← actO_smul', hu₀e, actO_actO_inv]
  refine ⟨partAt (1 - cA D e) X, hv ▸ hu₀, ?_, ?_⟩
  · rw [partAt_eq_smul, partAt_eq_smul, smul_comm (cA D e) (2 : ℕ) X, ← smul_add, ← add_smul]
    congr 1
    rw [add_sub_cancel, one_smul]
  · have hce : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
    have hint1 : finPart D (cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce])
    have hce' : (1 - cA D e) * (1 - cA D e) = 1 - cA D e := by linear_combination hce
    have hint2 : finPart D (1 - cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce'])
    have hstar : ∀ v : Fin S.rank → D.host.E, v ∈ std ↔ star v ∈ std := by
      have : ∀ v : Fin S.rank → D.host.E, v ∈ std → star v ∈ std := fun v hv =>
        (GlobalTheory.SW.Base.mem_stdL _).2 fun a => GlobalTheory.SW.Base.isIntegral_cc ((GlobalTheory.SW.Base.mem_stdL _).1 hv a)
      exact fun v => ⟨this v, fun h => by simpa using this _ h⟩
    have hlat := GlobalTheory.Ker.LatTens.latO_eq_hatA D S T C std std ΛT C.X.Λ hstar hAA
    have hxΛ : x ∈ hatA S T (tens std C.X.Λ) := by
      rw [hx, GlobalTheory.Ker.SignVac.finW_eq]
      exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.TensLatMove.intAf_one (D := D)) (tens_mono _ Submodule.smul_le_right hy')
    rw [← hlat] at hxΛ
    have hP := Formalism.IndefR.Fin.latO_smul_mem S T std ΛT hint1 hxΛ
    have hR := Formalism.IndefR.Fin.latO_smul_mem S T std ΛT hint2 hxΛ
    have hpair := GlobalTheory.LatVac.char_sympl_eq_one C.std (GlobalTheory.Ker.Base.selfDualC_stdL hS) hT hP hR
    have hpair' : C.ψ (symplO S T (cA D e • X) ((1 - cA D e) • X)) = 1 := by
      rw [hX, ← actO_smul', ← actO_smul', GlobalTheory.SymplOInv.symplO_actO]; exact hpair
    rw [partAt_eq_smul, partAt_eq_smul, smul_comm (cA D e) (2 : ℕ) X, two_nsmul, two_nsmul,
      GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self, GlobalTheory.LatVac.symplO_add_right,
      AddChar.map_add_eq_mul, hpair', one_mul]

end GlobalTheory.LiftLevel.MovedClass

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedClass_eq_part_add_two_movedShiftedPoint : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1 := by
  atlas_forward_decl GlobalTheory.LiftLevel.MovedClass.moved_class
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

def vmvBil (E : Type) [Field E] [NumberField E] (n r : ℕ) :
    (Fin n → E) →ₗ[𝓞 E] (Fin r → E) →ₗ[𝓞 E] Matrix (Fin n) (Fin r) E :=
  LinearMap.mk₂ (𝓞 E) (fun v u => vecMulVec v u)
    (fun v v' u => by ext i j; simp [vecMulVec, add_mul])
    (fun a v u => by ext i j; simp [vecMulVec, smul_mul_assoc])
    (fun v u u' => by ext i j; simp [vecMulVec, mul_add])
    (fun a v u => by ext i j; simp [vecMulVec, mul_smul_comm])

theorem tens_quot_finite {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (L : Lt E r)
    (hΛ : Λ.FG) (hL : L.FG) (𝔞 𝔪 : Ideal (𝓞 E)) (hm : 𝔪 ≠ ⊥) :
    Finite (tens Λ (𝔞 • L) ⧸ (tens Λ ((𝔞 * 𝔪) • L)).addSubgroupOf (tens Λ (𝔞 • L))) := by
  set A := tens Λ (𝔞 • L) with hA
  set B := tens Λ ((𝔞 * 𝔪) • L) with hB
  have hM : (Submodule.map₂ (vmvBil E n r) Λ L).FG := hΛ.map₂ _ hL
  have hMZ : ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).FG := hM.restrictScalars
  have hle : A.toIntSubmodule ≤ (Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ := by
    intro x hx
    have hsub : A ≤ ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).toAddSubgroup := by
      rw [hA, tens, AddSubgroup.closure_le]
      rintro y ⟨v, hv, u, hu, rfl⟩
      exact Submodule.apply_mem_map₂ (vmvBil E n r) hv (Submodule.smul_le_right hu)
    exact hsub hx
  have hAfg : A.toIntSubmodule.FG :=
    (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _ hMZ)) _ hle
  haveI : AddGroup.FG A := by
    have : Module.Finite ℤ A.toIntSubmodule := Module.Finite.iff_fg.mpr hAfg
    exact (Module.Finite.iff_addGroup_fg).mp this
  set N := Ideal.absNorm 𝔪 with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.mp h))
  have hNA : ∀ x ∈ A, N • x ∈ B := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u, hu, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨v, hv, N • u, ?_, ?_⟩
      · have h1 : ((N : 𝓞 E)) • u ∈ 𝔪 • (𝔞 • L) := Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hu
        rw [← Submodule.mul_smul, mul_comm] at h1
        rwa [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      · ext i j; simp [vecMulVec]; ring
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  haveI : AddGroup.FG (A ⧸ B.addSubgroupOf A) := AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hNpos, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hNA x x.2

theorem lvCls_finite : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X), Finite (GlobalTheory.LiftLevel.LvCls C Lv) := by
  intro D S T C Lv
  exact tens_quot_finite _ _ (Submodule.fg_span (Set.finite_range _)) C.X.Λ_fg _ _ Lv.ne_bot

end GlobalTheory.LiftLevel

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_levelDatumClasses : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X), Finite (GlobalTheory.LiftLevel.LvCls C Lv) := by
  atlas_forward_decl GlobalTheory.LiftLevel.lvCls_finite
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem lift_level_datum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ (Lv : GlobalTheory.SW.Level C.X) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (L : AddSubgroup (WO S T)), IdemTwo Lv.w ∧ (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ k₀ ∈ GfC S ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) ∧ Finite (GlobalTheory.LiftLevel.LvCls C Lv) ∧ (∀ x ∈ L, IsHalf (cA D e) x) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) ∧ (∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1) ∧ ∀ x, GlobalTheory.LiftLevel.thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : GlobalTheory.LiftLevel.LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) * GlobalTheory.LiftLevel.indL L (x + GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) := by
  intro D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨hI1, hI2, hI3, hI4⟩ := GlobalTheory.T.conjugatePlacesProductIdeal_proper_odd_coprime D Pg Q e hPg h2 he
  obtain ⟨a, ha, hgen⟩ := GlobalTheory.T.exists_idele_generates_polarisationIdeal_conjPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₀, Λ', hmov, hM⟩ := GlobalTheory.T.exists_finite_unitary_mover_standard_lattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a ha
  obtain ⟨Lv, h𝔪, hw, hJ, hD2⟩ := GlobalTheory.T.conjugatePlaces_liftLevelDatum_eq D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ ha hmov hgen hI1 hI2 hI3 hI4
  obtain ⟨m1, hm1, hm1'⟩ := GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨m2, hm2, hm2'⟩ := GlobalTheory.T.nsmul_mem_lift_points_of_completed_hom_lattice_half D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hfin := GlobalTheory.T.finite_levelDatumClasses D S T C Lv
  refine ⟨Lv, k₀, Λ', liftL S T βS βT Pg Q e, hw, ?_, hJ, hmov.1, hM, hfin, fun x hx => hx.1,
    ⟨m1, hm1, hm1'⟩, ⟨m2, hm2, hm2'⟩,
    fun u hu => ⟨GlobalTheory.T.shiftedTensorLatticePart_mem_liftLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu, fun t ht => GlobalTheory.T.liftGroupPoints_pair_trivial_shiftedTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu t ht, GlobalTheory.T.scaledTensorLattice_le_completedHomLattice_offPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu⟩,
    GlobalTheory.T.movedClass_eq_part_add_two_movedShiftedPoint D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪, GlobalTheory.T.liftVectorDatum_eq_sum_levelClassIndicators D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 hfin hD2⟩
  intro PP hPP
  rw [h𝔪]
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hPP))

end GlobalTheory.LiftLevel

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_level_datum_sum_of_translates : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ (Lv : GlobalTheory.SW.Level C.X) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (L : AddSubgroup (WO S T)), IdemTwo Lv.w ∧ (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ k₀ ∈ GfC S ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) ∧ Finite (GlobalTheory.LiftLevel.LvCls C Lv) ∧ (∀ x ∈ L, IsHalf (cA D e) x) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) ∧ (∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1) ∧ ∀ x, GlobalTheory.LiftLevel.thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : GlobalTheory.LiftLevel.LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) * GlobalTheory.LiftLevel.indL L (x + GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) := by
  atlas_forward_decl GlobalTheory.LiftLevel.lift_level_datum
end
