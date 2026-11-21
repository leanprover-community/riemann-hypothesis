import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LinearCoefficientData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceOffLevelSetProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorOffDifferent
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCoefficientElementarySymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyScaledInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.HeckeOrthSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_dvd_different (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ¬ P.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E) := by
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := D.host.isCMField_hostE
    exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  haveI := P.isPrime
  exact not_dvd_differentIdeal_iff.2 (Algebra.unramified_iff_forall.1 hU ⟨P.asIdeal, P.isPrime⟩)

end GlobalTheory.HeckeOrthSum
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.LocalReps.exists_isCosetRep : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (α : GA D V), IsPrimeIdem P e f → SuppF V f α → ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V f k} α R := by
  intro D V P e f α hP hα
  rcases id hP with ⟨he, rfl⟩ | ⟨rfl, -⟩
  · exact (GlobalTheory.SplitPlace.split_local V P e he).2.1 α hα
  · exact (GlobalTheory.InertDoubleCoset.inert_double_cosets V P f hP
      (GlobalTheory.SphericalComm.exists_unif_of_not_dvd P (GlobalTheory.HeckeOrthSum.not_dvd_different D P)) α hα).2.1
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_representatives_of_support : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (α : GA D V), IsPrimeIdem P e f → SuppF V f α → ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V f k} α R := by
  atlas_forward_decl GlobalTheory.LocalReps.exists_isCosetRep
end

section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalIsometryEqualRank

theorem exists_of_frames {A : Type} [CommRing A] (σ : A →+* A) {m n : ℕ} (hr : m = n)
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin m) (Fin m) A) (h : GL (Fin n) A) (h' : GL (Fin m) A)
    (h2 : (h.1.map σ)ᵀ * J * h.1 = 1) (h2' : (h'.1.map σ)ᵀ * J' * h'.1 = 1) (S : Subring A) :
    ∃ (φ : Matrix (Fin m) (Fin n) A) (ψ : Matrix (Fin n) (Fin m) A), φ * ψ = 1 ∧ ψ * φ = 1 ∧
      ((φ.map σ)ᵀ * J' : Matrix (Fin n) (Fin m) A) * φ = J ∧
      ∀ x, (∀ i, (h⁻¹).1.mulVec x i ∈ S) ↔ (∀ i, (h'⁻¹).1.mulVec (φ.mulVec x) i ∈ S) := by
  subst hr
  refine ⟨(h' * h⁻¹).1, (h * h'⁻¹).1, ?_, ?_, ?_, fun x => ?_⟩
  · rw [← Units.val_mul]; simp
  · rw [← Units.val_mul]; simp
  · have e : ((h⁻¹).1.map σ)ᵀ * (h.1.map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
    have e2 : h.1 * (h⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc ((h⁻¹).1.map σ)ᵀ * (h'.1.map σ)ᵀ * J' * (h'.1 * (h⁻¹).1)
        = ((h⁻¹).1.map σ)ᵀ * ((h'.1.map σ)ᵀ * J' * h'.1) * (h⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = ((h⁻¹).1.map σ)ᵀ * ((h.1.map σ)ᵀ * J * h.1) * (h⁻¹).1 := by rw [h2, h2']
      _ = (((h⁻¹).1.map σ)ᵀ * (h.1.map σ)ᵀ) * J * (h.1 * (h⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [e, e2, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]

section CM
attribute [local instance] IsCMField.starRing

theorem exists_of_cm {E : Type} [Field E] [NumberField E] [IsCMField E] (hc : CMData (maximalRealSubfield E) E)
    (V V' : HSpace E) (hr : V'.rank = V.rank) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E))
      (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)),
      φ * ψ = 1 ∧ ψ * φ = 1 ∧
      (Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) φ * JR (Fv (maximalRealSubfield E) v) V'.gram :
        Matrix (Fin V.rank) (Fin V'.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) * φ =
        JR (Fv (maximalRealSubfield E) v) V.gram ∧
      ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔
        φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V' v := by
  obtain ⟨h, h1, h2⟩ := exists_orthonormal hc V v
  obtain ⟨h', h1', h2'⟩ := exists_orthonormal hc V' v
  obtain ⟨φ, ψ, a, b, c, d⟩ := exists_of_frames (sigR (Fv (maximalRealSubfield E) v) hc.sig) hr
    (JR (Fv (maximalRealSubfield E) v) V.gram) (JR (Fv (maximalRealSubfield E) v) V'.gram) h h' h2 h2' (ordAt E v)
  exact ⟨φ, ψ, a, b, c, fun x => (h1 x).trans ((d x).trans (h1' _).symm)⟩

end CM

theorem exists_local_isometry : ∀ (D : D7) (V V' : Formalism.BasicNotions.TH.HSp D), V'.rank = V.rank → ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)) (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)), φ * ψ = 1 ∧ ψ * φ = 1 ∧ (Formalism.UG.cT (sigR (Fv D.host.F v) D.sp.cm.sig) φ * JR (Fv D.host.F v) V'.gram : Matrix (Fin V.rank) (Fin V'.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)) * φ = JR (Fv D.host.F v) V.gram ∧ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V' v := by
  intro D V V' hr v
  have := D.host.isCMField_hostE
  have key := exists_of_cm (E := D.host.E) D.sp.cm V V' hr v
  exact key

end GlobalTheory.LocalIsometryEqualRank
end

section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsomTransport

section Ring

variable {A : Type} [CommRing A] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def conjGL (φ : Matrix m n A) (ψ : Matrix n m A) (h1 : φ * ψ = 1) (h2 : ψ * φ = 1) (g : GL n A) : GL m A where
  val := φ * g.1 * ψ
  inv := φ * (g⁻¹).1 * ψ
  val_inv := by
    rw [Matrix.mul_assoc (φ * g.1), ← Matrix.mul_assoc ψ, ← Matrix.mul_assoc ψ, h2, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc φ, Units.mul_inv, Matrix.mul_one, h1]
  inv_val := by
    rw [Matrix.mul_assoc (φ * (g⁻¹).1), ← Matrix.mul_assoc ψ, ← Matrix.mul_assoc ψ, h2, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc φ, Units.inv_mul, Matrix.mul_one, h1]

omit [DecidableEq n] in
theorem conj_unitary (σ : A →+* A) (φ : Matrix m n A) (ψ : Matrix n m A) (h1 : φ * ψ = 1)
    (J : Matrix n n A) (J' : Matrix m m A) (hJ : Formalism.UG.cT σ φ * J' * φ = J) (g : Matrix n n A)
    (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT σ (φ * g * ψ) * J' * (φ * g * ψ) = J' := by
  have e1 : Formalism.UG.cT σ (φ * g * ψ) * J' * (φ * g * ψ) =
      Formalism.UG.cT σ ψ * (Formalism.UG.cT σ g * (Formalism.UG.cT σ φ * J' * φ) * g) * ψ := by
    simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
  have e2 : Formalism.UG.cT σ (φ * ψ) * J' * (φ * ψ) =
      Formalism.UG.cT σ ψ * (Formalism.UG.cT σ φ * J' * φ) * ψ := by
    simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
  rw [e1, hJ, hg, ← hJ, ← e2, h1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

end Ring

theorem stab_iff_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    (g : HA (AF F) hc.sig V.gram) (hg : ∀ w, w ≠ v → locMat hc V w g = 1) :
    Stab hc V g ↔ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔
      (locMat hc V v g).1.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  have hev : ∀ w (y : Fin V.rank → Af F ⊗[F] E),
      (fun i => evF E w ((finMat hc.sig V.gram g).mulVec y i)) =
        (locMat hc V w g).1.mulVec fun i => evF E w (y i) := fun w y => by
    funext i
    rw [locMat_val]
    exact RingHom.map_mulVec (evF E w) _ y i
  constructor
  · intro hs x
    have hx : ∀ w, w ≠ v → (fun i => evF E w (sgT E v (x i))) = 0 := fun w hw =>
      funext fun i => evF_sgT_ne hw _
    have hxv : (fun i => evF E v (sgT E v (x i))) = x := funext fun i => evF_sgT_self v _
    have := hs fun i => sgT E v (x i)
    rw [mem_lamHat_iff, mem_lamHat_iff] at this
    simp only [hev] at this
    constructor
    · intro h0
      have h1 := this.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [hxv]; exact h0
        · rw [hx w hw]; exact zero_mem _) v
      rwa [hxv] at h1
    · intro h0
      have h1 := this.2 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [hxv]; exact h0
        · rw [hx w hw, Matrix.mulVec_zero]; exact zero_mem _) v
      rwa [hxv] at h1
  · intro hs y
    rw [mem_lamHat_iff, mem_lamHat_iff]
    refine forall_congr' fun w => ?_
    rw [hev]
    by_cases hw : w = v
    · subst hw; exact hs _
    · rw [hg w hw, Units.val_one, Matrix.one_mulVec]

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V V' : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (f : AF F ⊗[F] E) (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv F v ⊗[F] E)) (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv F v ⊗[F] E)), IsIdemOf E v f → φ * ψ = 1 → ψ * φ = 1 → (∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V' v) → (Formalism.UG.cT (sigR (Fv F v) hc.sig) φ * JR (Fv F v) V'.gram : Matrix (Fin V.rank) (Fin V'.rank) (Fv F v ⊗[F] E)) * φ = JR (Fv F v) V.gram → ∀ g, Supp hc V f g → ∃ g', Supp hc V' f g' ∧ (locMat hc V' v g').1 = φ * (locMat hc V v g).1 * ψ ∧ (Stab hc V' g' ↔ Stab hc V g) := by
  intro F E _ _ _ _ _ _ hc V V' v f φ ψ hf h1 h2 hL hJ g hg
  have hu : conjGL φ ψ h1 h2 (locMat hc V v g) ∈ HR (Fv F v) hc.sig V'.gram :=
    conj_unitary _ φ ψ h1 _ _ hJ _ (locMat_mem hc V v g)
  obtain ⟨g', hg', e⟩ := (GlobalTheory.SuppLocal.supp_local F E hc V' v f hf).2.2 _ hu
  have e' : (locMat hc V' v g').1 = φ * (locMat hc V v g).1 * ψ := by rw [e]; rfl
  refine ⟨g', hg', e', ?_⟩
  rw [stab_iff_loc hc V' v g' ((GlobalTheory.SuppLocal.supp_iff hc V' hf g').1 hg').2,
    stab_iff_loc hc V v g ((GlobalTheory.SuppLocal.supp_iff hc V hf g).1 hg).2, e']
  constructor
  · intro hs x
    have := hs (φ.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mulVec_mulVec] at this
    rw [hL, hL ((locMat hc V v g).1.mulVec x)]
    exact this
  · intro hs y
    have := hs (ψ.mulVec y)
    rw [hL, hL ((locMat hc V v g).1.mulVec _), Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    exact this

end GlobalTheory.IsomTransport
end

section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

noncomputable def evVec {n : Type} (v : HeightOneSpectrum (𝓞 F)) (x : n → Af F ⊗[F] E) : n → Fv F v ⊗[F] E :=
  fun i => evF E v (x i)

theorem evVec_mul {n : Type} (v : HeightOneSpectrum (𝓞 F)) (ε : Af F ⊗[F] E) (x : n → Af F ⊗[F] E) :
    evVec v (fun a => ε * x a) = evF E v ε • evVec v x := by
  funext a
  exact map_mul _ _ _

theorem evVec_mulVec {m n : Type} [Fintype n] (v : HeightOneSpectrum (𝓞 F))
    (A : Matrix m n (Af F ⊗[F] E)) (z : n → Af F ⊗[F] E) :
    evVec v (A.mulVec z) = (A.map (evF E v)).mulVec (evVec v z) := by
  funext a
  exact RingHom.map_mulVec _ _ _ _

theorem evVec_sgT {n : Type} (v : HeightOneSpectrum (𝓞 F)) (y : n → Fv F v ⊗[F] E) :
    evVec v (fun i => sgT E v (y i)) = y := by
  funext a
  exact evF_sgT_self _ _

theorem mul_eq_iff {n : Type} {v : HeightOneSpectrum (𝓞 F)} {ε : Af F ⊗[F] E}
    (hε : ∀ w, w ≠ v → evF E w ε = 0) (x x' : n → Af F ⊗[F] E) :
    ((fun a => ε * x a) = fun a => ε * x' a) ↔ evF E v ε • evVec v x = evF E v ε • evVec v x' := by
  rw [← evVec_mul, ← evVec_mul]
  refine ⟨fun h => by rw [h], fun h => funext fun a => evF_ext fun w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact congrFun h a
  · rw [map_mul, map_mul, hε w hw, zero_mul, zero_mul]

theorem evVec_newBasis {m n : ℕ} (hr : m = n) (v : HeightOneSpectrum (𝓞 F))
    (φ : Matrix (Fin m) (Fin n) (Fv F v ⊗[F] E)) (B : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))
    (z : Fin m → Af F ⊗[F] E) :
    evVec v (((φ.map (sgT E v) * B).submatrix id (Fin.cast hr)).mulVec z) =
      φ.mulVec (evVec v (B.mulVec fun i => z (Fin.cast hr.symm i))) := by
  subst hr
  have h : (φ.map (sgT E v)).map (evF E v) = φ := by
    ext i j : 1
    exact evF_sgT_self _ _
  show evVec v ((φ.map (sgT E v) * B).mulVec z) = φ.mulVec (evVec v (B.mulVec z))
  rw [← Matrix.mulVec_mulVec, evVec_mulVec, h]

theorem mul_mem_lamHat_iff [NumberField E] [StarRing E] (V : HSpace E) {v : HeightOneSpectrum (𝓞 F)}
    {ε : Af F ⊗[F] E} (hε : ∀ w, w ≠ v → evF E w ε = 0) (x : Fin V.rank → Af F ⊗[F] E) :
    (fun a => ε * x a) ∈ lamHat F V ↔ evF E v ε • evVec v x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  rw [mem_lamHat_iff, ← evVec_mul]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact h
  · simp only [map_mul, hε w hw, zero_mul]; exact zero_mem _

theorem divG_of_local_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V V' : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (f : AF F ⊗[F] E) (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv F v ⊗[F] E)) (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv F v ⊗[F] E)), IsIdemOf E v f → φ * ψ = 1 → ψ * φ = 1 → (∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V' v) → ∀ (hr : V'.rank = V.rank) (e : AF F ⊗[F] E) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram) (g' : HA (AF F) hc.sig V'.gram), f * e = e → (locMat hc V' v g').1 = φ * (locMat hc V v g).1 * ψ → DivG hc V e ϖ d g → DivG hc V' e ϖ (fun i => d (Fin.cast hr i)) g' := by
  intro F E _ _ _ _ _ _ hc V V' v f φ ψ hf hφψ hψφ hL hr e ϖ d g g' hfe hg ⟨B, h1, h2, h3, h4⟩
  have hε : ∀ w, w ≠ v → evF E w (finP F E e) = 0 := ((GlobalTheory.SuppLocal.idem_mul_iff hf e).1 hfe).2
  have hback : ∀ y, φ.mulVec (ψ.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hφψ, Matrix.one_mulVec]
  have hback' : ∀ y, ψ.mulVec (φ.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hψφ, Matrix.one_mulVec]
  have hψ : ∀ y ∈ lamHat F V', (fun i => sgT E v (ψ.mulVec (evVec v y) i)) ∈ lamHat F V := fun y hy =>
    GlobalTheory.PlaceDiv.sgT_mem_lamHat V v ((hL _).2 (by rw [hback]; exact (mem_lamHat_iff V' y).1 hy v))
  have hφ : ∀ y ∈ lamHat F V, (fun i => sgT E v (φ.mulVec (evVec v y) i)) ∈ lamHat F V' := fun y hy =>
    GlobalTheory.PlaceDiv.sgT_mem_lamHat V' v ((hL _).1 ((mem_lamHat_iff V y).1 hy v))
  have hg' : ∀ y, evVec v ((finMat hc.sig V'.gram g').mulVec y) =
      φ.mulVec (((finMat hc.sig V.gram g).map (evF E v)).mulVec (ψ.mulVec (evVec v y))) := fun y => by
    rw [evVec_mulVec, ← locMat_val, hg, locMat_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine ⟨(φ.map (sgT E v) * B).submatrix id (Fin.cast hr), fun z hz => ?_, fun y hy => ?_, fun y hy => ?_,
    fun z hz => ?_⟩
  · rw [mul_mem_lamHat_iff V' hε, evVec_newBasis, ← Matrix.mulVec_smul, ← hL, ← mul_mem_lamHat_iff V hε]
    exact h1 _ fun i => hz _
  · obtain ⟨z, hz, e2⟩ := h2 _ (hψ y hy)
    refine ⟨fun i => z (Fin.cast hr i), fun i => hz _, ?_⟩
    rw [mul_eq_iff hε, evVec_sgT] at e2
    rw [mul_eq_iff hε, evVec_newBasis, ← Matrix.mulVec_smul]
    refine Eq.trans ?_ (congrArg φ.mulVec e2)
    rw [Matrix.mulVec_smul, hback]
  · obtain ⟨z, hz, e2⟩ := h3 _ (hψ y hy)
    refine ⟨fun i => z (Fin.cast hr i), fun i => hz _, ?_⟩
    rw [mul_eq_iff hε, evVec_mulVec, evVec_sgT] at e2
    rw [mul_eq_iff hε, evVec_newBasis, hg', ← Matrix.mulVec_smul φ, ← Matrix.mulVec_smul φ]
    exact congrArg φ.mulVec e2
  · obtain ⟨y, hy, e2⟩ := h4 (fun i => z (Fin.cast hr.symm i)) fun i => hz _
    refine ⟨_, hφ y hy, ?_⟩
    rw [mul_eq_iff hε, evVec_mulVec] at e2
    rw [mul_eq_iff hε, evVec_newBasis, hg', evVec_sgT, hback', ← Matrix.mulVec_smul φ, ← Matrix.mulVec_smul φ]
    exact congrArg φ.mulVec e2

end GlobalTheory.DivTransport
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivMove

theorem exists_place {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), GlobalTheory.PlaceComp.IsIdemOf D.host.E v f ∧ f * e = e := by
  rcases h with ⟨he, rfl⟩ | ⟨rfl, ⟨v, ε, ⟨a, rfl, h1, h2⟩, he⟩, -⟩
  · obtain ⟨hee, hec, v, ε, ⟨a, rfl, h1, h2⟩, hs⟩ := he.1
    refine ⟨v, ?_, ?_⟩
    · rw [hs]; exact GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2
    · rw [add_mul, hee, mul_comm, hec, add_zero]
  · have hi : GlobalTheory.PlaceComp.IsIdemOf D.host.E v f := by
      rw [he]; exact GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2
    exact ⟨v, hi, (GlobalTheory.SuppLocal.idem_mul_iff hi f).2 ⟨hi.1, hi.2.2⟩⟩

theorem exists_divAt_of_rank_eq : ∀ {D : D7} (V V' : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), V'.rank = V.rank → IsPrimeIdem P e f → SuppF V f α → DivAt V e ϖ d α → ∃ α' : GA D V', SuppF V' f α' ∧ DivAt V' e ϖ d α' := by
  intro D V V' P e f ϖ d α hr hP hα hd
  obtain ⟨v, hf, hfe⟩ := exists_place hP
  obtain ⟨φ, ψ, h1, h2, hJ, hL⟩ := GlobalTheory.LocalIsometryEqualRank.exists_local_isometry D V V' hr v
  obtain ⟨α', hs, hm, -⟩ :=
    GlobalTheory.IsomTransport.transport D.host.F D.host.E D.sp.cm V V' v f φ ψ hf h1 h2 hL hJ α hα
  exact ⟨α', hs, hd.1.trans hr.symm,
    GlobalTheory.DivTransport.divG_of_local_isometry D.host.F D.host.E D.sp.cm V V' v f φ ψ hf h1 h2 hL hr e ϖ
      (fun i => d.getD i.1 0) α α' hfe hm hd.2⟩

end GlobalTheory.DivMove
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_support_transfer_rank : ∀ {D : D7} (V V' : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), V'.rank = V.rank → IsPrimeIdem P e f → SuppF V f α → DivAt V e ϖ d α → ∃ α' : GA D V', SuppF V' f α' ∧ DivAt V' e ϖ d α' := by
  atlas_forward_decl GlobalTheory.DivMove.exists_divAt_of_rank_eq
end

section
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_coefficient_elementary_symm : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) (k : ℕ), ParGL P n lab c s → k ≤ n → lab (dualLab (splitLab n k)) → c (dualLab (splitLab n k)) = (qV E P : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) * s.esymm k := by
  first | exact @GlobalTheory.SphPar.parGL_dualLab_splitLab | exact GlobalTheory.SphPar.parGL_dualLab_splitLab | (intros; apply GlobalTheory.SphPar.parGL_dualLab_splitLab <;> assumption)
end

section
section
noncomputable section

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.InvTranspose

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

def flipM (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := A.transpose.submatrix Fin.rev Fin.rev

theorem flipM_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) : flipM A i j = A j.rev i.rev := rfl

theorem flipM_mul (A B : Matrix (Fin n) (Fin n) R) : flipM (A * B) = flipM B * flipM A := by
  unfold flipM
  rw [Matrix.transpose_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ (Fin.revPerm : Fin n ≃ Fin n) _).symm

theorem flipM_one : flipM (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  simp [flipM_apply, Matrix.one_apply, eq_comm]

theorem flipM_flipM (A : Matrix (Fin n) (Fin n) R) : flipM (flipM A) = A := by
  ext i j
  simp [flipM_apply]

theorem flipM_diagonal (a : Fin n → R) : flipM (Matrix.diagonal a) = Matrix.diagonal (fun i => a i.rev) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [flipM_apply]
  · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
    simp [flipM_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h']

def theta : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨flipM ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R), flipM (g : Matrix (Fin n) (Fin n) R),
    by rw [← flipM_mul, Units.mul_inv, flipM_one], by rw [← flipM_mul, Units.inv_mul, flipM_one]⟩
  map_one' := by
    apply Units.ext
    simp [flipM_one]
  map_mul' g h := by
    apply Units.ext
    simp only [mul_inv_rev, Units.val_mul, flipM_mul]

theorem coe_theta (g : GL (Fin n) R) :
    (theta g : Matrix (Fin n) (Fin n) R) = flipM ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := rfl

theorem theta_theta (g : GL (Fin n) R) : theta (theta g) = g := by
  apply Units.ext
  rw [coe_theta]
  exact flipM_flipM _

end Ring

section Field

variable {L : Type} [Field L] {n : ℕ}

theorem theta_mem {O : Subring L} {g : GL (Fin n) L} (hg : g ∈ GLint (Fin n) O) : theta g ∈ GLint (Fin n) O := by
  obtain ⟨k, rfl⟩ := hg
  refine ⟨theta k, ?_⟩
  apply Units.ext
  rw [coe_theta, ← map_inv]
  rfl

theorem theta_upper {b : GL (Fin n) L} (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((theta b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  intro i j hij
  rw [coe_theta, flipM_apply]
  exact Formalism.UG.P.spherical_upper_inv b hb (Fin.rev_lt_rev.2 hij)

theorem theta_diag {b : GL (Fin n) L} (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) (i : Fin n) :
    ((theta b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * (b : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 := by
  rw [coe_theta, flipM_apply, ← Formalism.UG.P.spherical_diag_mul _ _ (Formalism.UG.P.spherical_upper_inv b hb) hb,
    Units.inv_mul, Matrix.one_apply_eq]

theorem getD_dualLab' (d : List ℤ) (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i.1 0 = -(d.getD i.rev.1 0) := by
  subst hd
  have h1 : i.1 < (dualLab d).length := by simp only [dualLab, List.length_reverse, List.length_map]; exact i.2
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  congr 2
  omega

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem hasDiv_theta {O : Subring L} {d : List ℤ} (hd : d.length = n) {g : GL (Fin n) L} (h : HasDiv O d g) :
    HasDiv O (dualLab d) (theta g) := by
  obtain ⟨ϖ, hϖ, a, ha, b, hb, e⟩ := h
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  let D : GL (Fin n) L := ⟨Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0),
    Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0))),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
       rw [← zpow_add₀ h0, add_neg_cancel, zpow_zero],
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
       rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]⟩
  have hg : g = a * D * b := Units.ext e
  refine ⟨ϖ, hϖ, theta a, theta_mem ha, theta b, theta_mem hb, ?_⟩
  rw [hg, map_mul, map_mul, Units.val_mul, Units.val_mul]
  congr 2
  rw [coe_theta]
  change flipM (Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0)))) = _
  rw [flipM_diagonal]
  congr 1
  funext i
  rw [getD_dualLab' d hd]

theorem divInd_theta (O : Subring L) {d : List ℤ} (hd : d.length = n) (g : GL (Fin n) L) :
    divInd O (dualLab d) g = divInd O d (theta g) := by
  have hdd : dualLab (dualLab d) = d := by simp [dualLab, List.map_reverse]
  have : HasDiv O (dualLab d) g ↔ HasDiv O d (theta g) := by
    constructor
    · intro h
      have := hasDiv_theta (by simpa [dualLab] using hd) h
      rwa [hdd] at this
    · intro h
      have := hasDiv_theta hd h
      rwa [theta_theta] at this
  unfold divInd
  by_cases h : HasDiv O d (theta g)
  · rw [Set.indicator_of_mem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_mem (s := {g | HasDiv O (dualLab d) g}) (this.2 h)]
    rfl
  · rw [Set.indicator_of_notMem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_notMem (s := {g | HasDiv O (dualLab d) g}) (fun h' => h (this.1 h'))]

theorem hasDiv_mul_right {O : Subring L} {d : List ℤ} {g k : GL (Fin n) L} (hk : k ∈ GLint (Fin n) O) (h : HasDiv O d g) :
    HasDiv O d (g * k) := by
  obtain ⟨ϖ, hϖ, a, ha, b, hb, e⟩ := h
  refine ⟨ϖ, hϖ, a, ha, b * k, mul_mem hb hk, ?_⟩
  rw [Units.val_mul, Units.val_mul, e]
  simp only [Matrix.mul_assoc]

theorem divInd_mul_right (O : Subring L) (d : List ℤ) (g k : GL (Fin n) L) (hk : k ∈ GLint (Fin n) O) :
    divInd O d (g * k) = divInd O d g := by
  unfold divInd
  by_cases h : HasDiv O d g
  · rw [Set.indicator_of_mem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_mem (s := {g | HasDiv O d g}) (hasDiv_mul_right hk h)]
    rfl
  · rw [Set.indicator_of_notMem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_notMem (s := {g | HasDiv O d g})]
    intro h'
    have := hasDiv_mul_right (inv_mem hk) h'
    rw [mul_inv_cancel_right] at this
    exact h this

end Field

theorem finsum_out_involution {G : Type} [Group G] (K : Subgroup G) (t : G →* G) (ht : ∀ g, t (t g) = g)
    (hK : ∀ k ∈ K, t k ∈ K) (F : G → ℂ) (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) :
    ∑ᶠ x : G ⧸ K, F (t x.out) = ∑ᶠ x : G ⧸ K, F x.out := by
  have hF' : ∀ g : G, F (QuotientGroup.mk (s := K) g).out = F g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hF _ _ k.2]
  let m : G ⧸ K → G ⧸ K := fun x => QuotientGroup.mk (t x.out)
  have hm : Function.Involutive m := fun x => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (t x.out)
    simp only [m]
    rw [hk, map_mul, ht, QuotientGroup.mk_mul_of_mem _ (hK _ k.2), QuotientGroup.out_eq']
  rw [← finsum_comp_equiv (hm.toPerm m) (f := fun x : G ⧸ K => F x.out)]
  exact finsum_congr fun x => (hF' _).symm

section Global

variable (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}

theorem ordV_of_mul_eq_one {x y : P.adicCompletion E} (h : x * y = 1) : ordV E P x = -ordV E P y := by
  have hx : x ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hy : y ≠ 0 := right_ne_zero_of_mul_eq_one h
  have h1 := Formalism.UG.P.spherical_ordV_mul E P x y hx hy
  have h2 := Formalism.UG.P.spherical_ordV_unit E P 1 1 (one_mem _) (one_mem _) (mul_one 1)
  rw [h, h2] at h1
  omega

theorem chiDelta_theta (α : Fin n → ℂ) {b : GL (Fin n) (P.adicCompletion E)}
    (hb : (b : Matrix (Fin n) (Fin n) (P.adicCompletion E)).BlockTriangular id) :
    chiDelta E P α (theta b) = chiDelta E P (fun i => (α i.rev)⁻¹) b := by
  unfold chiDelta
  rw [← Equiv.prod_comp (Fin.revPerm : Fin n ≃ Fin n) (fun i : Fin n => (α i.rev)⁻¹ ^ _ * _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ordV_of_mul_eq_one E P (theta_diag hb i)]
  simp only [Fin.revPerm_apply, Fin.rev_rev, inv_zpow']
  congr 2
  have : ((i.rev : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℂ) := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [this]
  push_cast
  ring

end Global

theorem exists_spherical_dual : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (α : Fin n → ℂ) (φ : GL (Fin n) (P.adicCompletion E) → ℂ), (∀ i, α i ≠ 0) → IsSpherical E P α φ → ∃ φ' : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P (fun i => (α i.rev)⁻¹) φ' ∧ φ' 1 = φ 1 ∧ ∀ d : List ℤ, d.length = n → hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) (dualLab d)) φ' 1 = hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 := by
  intro E _ _ P n α φ _ hφ
  refine ⟨fun g => φ (theta g), ?_, by simp, ?_⟩
  · intro b g k hb hk
    have hb' := (Formalism.UG.P.spherical_upper_iff b).1 hb
    simp only [map_mul]
    rw [hφ _ _ _ ((Formalism.UG.P.spherical_upper_iff _).2 (theta_upper hb')) (theta_mem hk), chiDelta_theta E P α hb']
  · intro d hd
    have h1 : ((1 : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)).BlockTriangular id :=
      Matrix.blockTriangular_one
    have hr : ∀ g, ∀ k ∈ GLint (Fin n) (Ov E P), φ (g * k) = φ g := fun g k hk => by
      have := hφ 1 g k ((Formalism.UG.P.spherical_upper_iff _).2 h1) hk
      rwa [one_mul, Formalism.UG.P.spherical_chiDelta_int E P α 1 h1 (one_mem _), one_mul] at this
    unfold hAct
    simp only [one_mul, divInd_theta _ hd]
    exact finsum_out_involution _ theta theta_theta (fun k => theta_mem)
      (fun g => divInd (Ov E P) d g • φ g) (fun g k hk => by rw [divInd_mul_right _ _ _ _ hk, hr g k hk])

end GlobalTheory.InvTranspose

end
end

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_function_dual_label : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (α : Fin n → ℂ) (φ : GL (Fin n) (P.adicCompletion E) → ℂ), (∀ i, α i ≠ 0) → IsSpherical E P α φ → ∃ φ' : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P (fun i => (α i.rev)⁻¹) φ' ∧ φ' 1 = φ 1 ∧ ∀ d : List ℤ, d.length = n → hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) (dualLab d)) φ' 1 = hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 := by
  atlas_forward_decl GlobalTheory.InvTranspose.exists_spherical_dual
end

section
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_divisor_dual_label : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (d : List ℤ) (g : GL (Fin n) L), (∀ x, Valued.v (σ x) = Valued.v x) → d.length = n → g ∈ GU σ n → HasDiv (intL L) d g → HasDiv (intL L) (dualLab d) g := by
  first | exact @GlobalTheory.DualDivU.hasDiv_dualLab | exact GlobalTheory.DualDivU.hasDiv_dualLab | (intros; apply GlobalTheory.DualDivU.hasDiv_dualLab <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_conjugate_place_uniformiser : ∀ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal → ∃ (σ : P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) (ϖ : P.adicCompletion D.host.E) (q : ℕ), IsConjAt P σ ∧ Formalism.UG.IsUnramInv ϖ σ q := by
  first | exact @GlobalTheory.FixedPrime.exists_isConjAt_isUnramInv | exact GlobalTheory.FixedPrime.exists_isConjAt_isUnramInv | (intros; apply GlobalTheory.FixedPrime.exists_isConjAt_isUnramInv <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct

namespace GlobalTheory.GapRegular

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Sep (S : SPar) : Prop := ∀ x ∈ S, ∀ y ∈ S, y.1 < x.1 → y.1 + 2 ≤ x.1

theorem Sep.dual {S : SPar} (h : Sep S) : Sep (dualPar S) := by
  intro x hx y hy hxy
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
  have := h y' hy' x' hx' (by simpa using hxy)
  simp only
  linarith

end GlobalTheory.GapRegular

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta
open Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Polynomial GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem GlobalTheory.HeckeParts
open Formalism.IndefR.Bridge (SplitOff)
open scoped TensorProduct

namespace GlobalTheory.SphPar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Par

open Formalism.UG

theorem exists_enum {n : ℕ} {s : Multiset ℂ} (h : s.card = n) : ∃ α : Fin n → ℂ, Finset.univ.val.map α = s := by
  induction s using Quotient.inductionOn with
  | h l =>
    have hl : l.length = n := by simpa using h
    subst hl
    refine ⟨l.get, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_get]
    rfl

theorem eq_of_esymm {n : ℕ} {s s' : Multiset ℂ} (h : s.card = n) (h' : s'.card = n) (he : ∀ k, k ≤ n → s.esymm k = s'.esymm k) :
    s = s' := by
  rw [← roots_multiset_prod_X_sub_C s, ← roots_multiset_prod_X_sub_C s', Multiset.prod_X_sub_X_eq_sum_esymm,
    Multiset.prod_X_sub_X_eq_sum_esymm, h, h']
  congr 1
  exact Finset.sum_congr rfl fun k hk => by rw [he k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

theorem kap_ne {q : ℕ} (hq : q ≠ 0) (n : ℕ) : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)) _).ne'

theorem frobPoly_inj {q n : ℕ} (hq : q ≠ 0) {s s' : Multiset ℂ} (h : frobPoly q n s = frobPoly q n s') : s = s' := by
  have e : ∀ u : Multiset ℂ, (frobPoly q n u).roots = u.map (· * (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) := fun u => by
    rw [← roots_multiset_prod_X_sub_C (u.map _), Multiset.map_map]
    rfl
  have := congrArg roots h
  rw [e, e] at this
  exact Multiset.map_injective (mul_left_injective₀ (kap_ne hq n)) this

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} {lab lab' : List ℤ → Prop}
  {c c' : List ℤ → ℂ} {s : Multiset ℂ}

theorem ParGL.eq (h : ParGL P n lab c s) (h' : ParGL P n lab c' s) {d : List ℤ} (hd : lab d) : c d = c' d := by
  obtain ⟨α, hα⟩ := exists_enum h.1
  obtain ⟨φ, h1, h2, -⟩ := Formalism.UG.Final.SphericalExists E P n α fun i e =>
    h.2.1 (hα ▸ Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)
  have := (h.2.2 α hα φ h1 d hd).symm.trans (h'.2.2 α hα φ h1 d hd)
  rwa [h2, mul_one, mul_one] at this

theorem ParGL.dual (h : ParGL P n lab (fun d => c (dualLab d)) s) (hl : ∀ d, lab' d → d.length = n ∧ lab (dualLab d)) :
    ParGL P n lab' c (s.map (·⁻¹)) := by
  have h0 : (0 : ℂ) ∉ s.map (·⁻¹) := fun e => by
    obtain ⟨a, ha, e⟩ := Multiset.mem_map.1 e
    exact h.2.1 (inv_eq_zero.1 e ▸ ha)
  refine ⟨by rw [Multiset.card_map, h.1], h0, fun α hα φ hφ d hd => ?_⟩
  obtain ⟨φ', h1, h2, h3⟩ := GlobalTheory.T.spherical_function_dual_label E P n α φ
    (fun i e => h0 (hα ▸ Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)) hφ
  have e : Finset.univ.val.map (fun i : Fin n => (α i.rev)⁻¹) = s := by
    have e1 : Finset.univ.val.map (fun i : Fin n => (α i.rev)⁻¹) = (Finset.univ.val.map α).map (·⁻¹) := by
      conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm]
      simp only [Multiset.map_map, Function.comp_def, Fin.revPerm_apply]
    rw [e1, hα, Multiset.map_map]
    simp
  have := h.2.2 _ e φ' h1 _ (hl d hd).2
  beta_reduce at this
  rwa [h3 d (hl d hd).1, dualLab_dualLab, h2] at this

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem ParU.eq [CompleteSpace L] (hU : IsUnramInv ϖ σ q) (h : ParU σ q n lab c s) (h' : ParU σ q n lab c' s) {d : List ℤ}
    (hd : lab d) : c d = c' d := by
  obtain ⟨α, hα⟩ := h.2.1
  obtain ⟨φ, h1, h2, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) α fun i e =>
    h.1 (hα ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)))))
  have := (h.2.2 α hα φ h1 d hd).symm.trans (h'.2.2 α hα φ h1 d hd)
  rwa [h2, mul_one, mul_one] at this

theorem ParU.dual (hU : IsUnramInv ϖ σ q) (h : ParU σ q n lab (fun d => c (dualLab d)) s)
    (hl : ∀ d, lab' d → d.length = n ∧ lab (dualLab d)) : ParU σ q n lab' c (s.map (·⁻¹)) := by
  obtain ⟨α₀, hα₀⟩ := h.2.1
  have hs : s.map (·⁻¹) = s := by rw [← hα₀, bcPar_map_inv]
  rw [hs]
  refine ⟨h.1, h.2.1, fun α hα φ hφ d hd => ?_⟩
  have := h.2.2 α hα φ hφ _ (hl d hd).2
  beta_reduce at this
  rw [dualLab_dualLab] at this
  rw [← this]
  congr 1
  funext g
  have hiff : HasDiv (intL L) d (g : GL (Fin n) L) ↔ HasDiv (intL L) (dualLab d) (g : GL (Fin n) L) :=
    ⟨GlobalTheory.T.unitary_divisor_dual_label L σ n d g hU.2.1 (hl d hd).1 g.2, fun h1 => by
      have := GlobalTheory.T.unitary_divisor_dual_label L σ n _ g hU.2.1 (by simpa [dualLab] using (hl d hd).1) g.2 h1
      rwa [dualLab_dualLab] at this⟩
  classical
  simp only [divInd, Set.indicator_apply, Set.mem_ofPred_eq, hiff, Pi.one_apply]

end U

variable [StarRing E]

theorem IsPar.dual (h : IsPar P n lab (fun d => c (dualLab d)) s) (hl : ∀ d, lab' d → d.length = n ∧ lab (dualLab d)) :
    IsPar P n lab' c (s.map (·⁻¹)) :=
  ⟨fun hP => (h.1 hP).dual hl, fun hP σ ϖ q h1 h2 => (h.2 hP σ ϖ q h1 h2).dual h2 hl⟩

end Par

theorem IsPar.eq {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ} {lab : List ℤ → Prop} {c c' : List ℤ → ℂ}
    {s : Multiset ℂ} (h : IsPar P n lab c s) (h' : IsPar P n lab c' s) {d : List ℤ} (hd : lab d) : c d = c' d := by
  by_cases hP : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal
  · obtain ⟨σ, ϖ, q, h1, h2⟩ := GlobalTheory.T.unramified_conjugate_place_uniformiser P hP
    exact (h.2 hP σ ϖ q h1 h2).eq h2 (h'.2 hP σ ϖ q h1 h2) hd
  · exact (h.1 hP).eq (h'.1 hP) hd

section Galois

open Formalism.ConjugateSelfDual

variable {D : D7}

abbrev GE (D : D7) : Type := G D.host.E (AlgebraicClosure D.host.E)

theorem normV_ne (P : HeightOneSpectrum (𝓞 D.host.E)) : normV P ≠ 0 :=
  show Ideal.absNorm P.asIdeal ≠ 0 from fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem finite_over {l : ℕ} (hl : l ≠ 0) : {P : HeightOneSpectrum (𝓞 D.host.E) | ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal}.Finite := by
  have h0 : ((l : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl
  refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 D.host.E)})
    (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem dense_frob (hC : GlobalTheory.TwSys.Cheb) {X : Set (HeightOneSpectrum (𝓞 D.host.E))} (hX : X.Finite) :
    Dense {g : GE D | ∃ P, P ∉ X ∧ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal ∧
      ∃ B : ValuationSubring (AlgebraicClosure D.host.E), IsPlaceOver (F := D.host.E) B P ∧ IsFrob (F := D.host.E) B (normV P) g} := by
  classical
  rw [dense_iff_inter_open]
  rintro W hW ⟨g, hg⟩
  have hV : IsOpen {s : GE D | s * g ∈ W} := hW.preimage (continuous_mul_const g)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV (by simpa using hg)
  obtain ⟨A, hA, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split D.host
  obtain ⟨v, hv, hd, -, B, hB, -, σ, hσ, hU'⟩ := hC D.host.E (AlgebraicClosure D.host.E) U.toSubgroup U.isOpen U.isNormal' g
    (hA.toFinset ∪ hX.toFinset)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
  have := hU hU'
  simp only [Set.mem_ofPred_eq, inv_mul_cancel_right] at this
  refine ⟨σ, this, v, hv.2, fun e => ?_, B, hB, hσ⟩
  obtain ⟨x, hx, hx'⟩ := hsp v hv.1 hd
  rw [← e, Formalism.L2.Col.mem_conjIdeal] at hx
  refine hx' _ (D.host.φ₀.injective ?_) hx
  exact (D.sp.cm.cmUnram.2.1 D.host.φ₀ x).trans (D.host.conjE_apply D.host.φ₀ x).symm

def FrobFam (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (lab : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → Prop)
    (c : Sys D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ f : GE D → Matrix (Fin n) (Fin n) (Qbar l), Continuous f ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D S P → ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
      ∃ s, IsPar P n (lab P) (c P) s ∧ ∀ (A : ValuationSubring (AlgebraicClosure D.host.E)) (g : GE D),
        IsPlaceOver (F := D.host.E) A P → IsFrob (F := D.host.E) A (normV P) g →
          (f g).charpoly.map (ι : Qbar l →+* ℂ) = frobPoly (normV P) n s

variable {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
  {lab : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → Prop} {c c' : Sys D}

theorem exists_prime_notMem (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ l : ℕ, l.Prime ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  by_contra h
  push Not at h
  have := P.asIdeal.sub_mem (h 3 Nat.prime_three) (h 2 Nat.prime_two)
  norm_num at this
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem FrobFam.eq (hC : GlobalTheory.TwSys.Cheb) {n : ℕ} (h : FrobFam n S lab c) (h' : FrobFam n S lab c')
    {X : Set (HeightOneSpectrum (𝓞 D.host.E))} (hX : X.Finite)
    (he : ∀ P, P ∉ X → Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal → OffS D S P ∧ ∀ k, k ≤ n →
      lab P (dualLab (splitLab n k)) ∧ c P (dualLab (splitLab n k)) = c' P (dualLab (splitLab n k)))
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) {d : List ℤ} (hd : lab P d) : c P d = c' P d := by
  obtain ⟨l, hl, hlP⟩ := exists_prime_notMem P
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨f, hf, h⟩ := h l ι
  obtain ⟨f', hf', h'⟩ := h' l ι
  have key : ∀ g, (f g).charpoly = (f' g).charpoly := fun g => by
    refine Polynomial.funext fun x => ?_
    rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
    refine congrFun (Continuous.ext_on (dense_frob hC (hX.union (finite_over hl.ne_zero)))
      (f := fun g => (Matrix.scalar (Fin n) x - f g).det) (g := fun g => (Matrix.scalar (Fin n) x - f' g).det)
      (continuous_const.sub hf).matrix_det (continuous_const.sub hf').matrix_det ?_) g
    rintro g ⟨Q, hQ, hs, B, hB, hg⟩
    rw [Set.mem_union, not_or] at hQ
    obtain ⟨ho, hk⟩ := he Q hQ.1 hs
    obtain ⟨s, h1, h2⟩ := h Q ho hQ.2
    obtain ⟨s', h1', h2'⟩ := h' Q ho hQ.2
    have e : s = s' := eq_of_esymm (h1.1 hs).1 (h1'.1 hs).1 fun k hkn => by
      have a := GlobalTheory.T.spherical_coefficient_elementary_symm _ Q n _ _ s k (h1.1 hs) hkn (hk k hkn).1
      have b := GlobalTheory.T.spherical_coefficient_elementary_symm _ Q n _ _ s' k (h1'.1 hs) hkn (hk k hkn).1
      rw [(hk k hkn).2, b] at a
      refine (mul_left_cancel₀ (fun e0 => ?_) a).symm
      exact normV_ne Q (Nat.cast_eq_zero.1 ((Complex.cpow_eq_zero_iff _ _).1 e0).1)
    have e2 : (f g).charpoly = (f' g).charpoly :=
      Polynomial.map_injective (ι : Qbar l →+* ℂ) ι.injective ((h2 B g hB hg).trans (e ▸ (h2' B g hB hg).symm))
    show (Matrix.scalar (Fin n) x - f g).det = (Matrix.scalar (Fin n) x - f' g).det
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, e2]
  obtain ⟨s, h1, h2⟩ := h P hP hlP
  obtain ⟨s', h1', h2'⟩ := h' P hP hlP
  obtain ⟨B, hB⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (AlgebraicClosure D.host.E) P
  obtain ⟨g, hg⟩ := ReciprocityTheory.Gal.exists_isFrob hB
  have e : s = s' := frobPoly_inj (normV_ne P) (by rw [← h2 B g hB hg, ← h2' B g hB hg, key])
  subst e
  exact h1.eq h1' hd

end Galois

section Labels

variable {D : D7} {V V' : HSp D} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : HeightOneSpectrum (𝓞 D.host.E)}
  {d : List ℤ}

theorem lab_of_div {J : Subgroup (GA D V)} {χ : GA D V → ℂ} (h : SphAt J χ P) (hS : OffS D S P) {e f : Formalism.L2.Theta.AE D}
    (hef : IsPrimeIdem P e f) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : d.Pairwise (fun a b => b ≤ a)) {α : GA D V} (hα : SuppF V f α) (hdiv : DivAt V e (ϖ : D.host.E) d α) :
    Lab V (J : Set (GA D V)) χ S P d := by
  obtain ⟨R, hR, hc⟩ := GlobalTheory.T.coset_representatives_of_support V P e f α hef hα
  refine ⟨R, e, f, ϖ, α, hS, hef, h1, h2, hd, (h e f hef).1, (h e f hef).2.1, hα, hdiv, hR, ?_⟩
  have : {k | k ∈ (J : Set (GA D V)) ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} :=
    Set.ext fun k => and_congr_left fun hk => (h e f hef).1 k hk
  rwa [this]

theorem Lab.off {J : Set (GA D V)} {χ : GA D V → ℂ} (h : Lab V J χ S P d) : OffS D S P ∧ d.length = V.rank := by
  obtain ⟨R, e, f, ϖ, α, hS, -, -, -, -, -, -, -, hdiv, -⟩ := h
  exact ⟨hS, hdiv.1⟩

theorem Lab.move {J : Set (GA D V)} {χ : GA D V → ℂ} (h : Lab V J χ S P d) (hr : V'.rank = V.rank) {J' : Subgroup (GA D V')}
    {χ' : GA D V' → ℂ} (h' : SphAt J' χ' P) : Lab V' (J' : Set (GA D V')) χ' S P d := by
  obtain ⟨R, e, f, ϖ, α, hS, hef, h1, h2, hd, -, -, hα, hdiv, -⟩ := h
  obtain ⟨α', h3, h4⟩ := GlobalTheory.T.divisor_support_transfer_rank V V' P e f ϖ d α hr hef hα hdiv
  exact lab_of_div h' hS hef h1 h2 hd h3 h4

theorem Lab.dual {J : Subgroup (GA D V)} {χ : GA D V → ℂ} (h : Lab V (J : Set (GA D V)) χ S P d) (h' : SphAt J χ P) :
    Lab V (J : Set (GA D V)) χ S P (dualLab d) := by
  obtain ⟨R, e, f, ϖ, α, hS, hef, h1, h2, hd, -, -, hα, hdiv, -⟩ := h
  obtain ⟨g1, -, g3, -⟩ := GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V
  obtain ⟨a, b, -⟩ := g3 P e f hef
  obtain ⟨⟨L, hL⟩, -⟩ := g1 f a b
  have he : e * e = e := by
    rcases hef with h | h
    · exact h.1.1.1
    · rw [← h.1]; exact a
  have hϖ : (ϖ : D.host.E) ≠ 0 := fun e0 => h2 (by rw [show ϖ = 0 from Subtype.ext e0]; exact zero_mem _)
  refine lab_of_div h' hS hef h1 h2 ?_ ((hL _).1 (L.inv_mem ((hL α).2 hα)))
    (GlobalTheory.DivDual.divAt_inv_and_mul V e ϖ d α he hϖ hdiv).1
  unfold dualLab
  rw [List.pairwise_reverse, List.pairwise_map]
  exact hd.imp fun hab => neg_le_neg hab

end Labels

section Record

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {s : ℕ}

variable (R) in

def LabY : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → Prop :=
  Lab (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R)

variable (R F) in

def GaloisRow : Prop :=
  R.Char F →
    (∀ c, OccE R c → HasGalois (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R)
      (dualSys c)) ∧
    ∀ i c, OccW R i c → HasGalois (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (badF R) c

end Record

end GlobalTheory.SphPar

end
end
