import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_decomposition_nonsplit_place : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ (g : GLoc D.sp.cm.sig V.gram v), ∃ q k : GLoc D.sp.cm.sig V.gram v, k ∈ stabLoc D.sp.cm.sig V.gram L v ∧ g = q * k ∧ ∃ β : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram q).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * β.1 := by
  first | exact @GlobalTheory.InertIwasawaLoc.eq_mul_stab_of_not_split | exact GlobalTheory.InertIwasawaLoc.eq_mul_stab_of_not_split | (intros; apply GlobalTheory.InertIwasawaLoc.eq_mul_stab_of_not_split <;> assumption)
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_decomposition_split_place : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ (g : GLoc D.sp.cm.sig V.gram v), ∃ q k : GLoc D.sp.cm.sig V.gram v, k ∈ stabLoc D.sp.cm.sig V.gram L v ∧ g = q * k ∧ ∃ β : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram q).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * β.1 := by
  first | exact @GlobalTheory.IwSplitFrame.iwasawa_span_split | exact GlobalTheory.IwSplitFrame.iwasawa_span_split | (intros; apply GlobalTheory.IwSplitFrame.iwasawa_span_split <;> assumption)
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.LocIwasawaGL

open scoped TensorProduct Matrix

def HasIw (R : Type) [CommRing R] (O : Subring R) : Prop :=
  ∀ (r : ℕ) (β : GL (Fin r) R), ∃ b α : GL (Fin r) R, b.1.BlockTriangular id ∧ (∀ i j, α.1 i j ∈ O) ∧
    (∀ i j, (α⁻¹).1 i j ∈ O) ∧ β = b * α

theorem hasIw_valuationSubring {K : Type} [Field K] (V : ValuationSubring K) : HasIw K V.toSubring := by
  intro r β
  obtain ⟨k, b, hb, h⟩ := GlobalTheory.ValIwasawa.iwasawa V K r β⁻¹
  refine ⟨b⁻¹, (Matrix.GeneralLinearGroup.map (algebraMap V K) k)⁻¹, ?_, ?_, ?_, ?_⟩
  · haveI : Invertible b.1 := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  · intro i j
    rw [← map_inv]
    exact (k⁻¹.1 i j).2
  · intro i j
    rw [inv_inv]
    exact (k.1 i j).2
  · rw [← mul_inv_rev, ← h, inv_inv]

theorem hasIw_of_equiv {R S : Type} [CommRing R] [CommRing S] {O : Subring R} {O' : Subring S} (φ : R ≃+* S)
    (hφ : ∀ y, y ∈ O ↔ φ y ∈ O') (h : HasIw S O') : HasIw R O := by
  intro r β
  obtain ⟨b, α, hb, h1, h2, e⟩ := h r (Matrix.GeneralLinearGroup.map (φ : R →+* S) β)
  have hinv : ∀ g : GL (Fin r) R,
      Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) (Matrix.GeneralLinearGroup.map (φ : R →+* S) g) = g :=
    fun g => by ext i j; simp
  refine ⟨Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) b, Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) α,
    ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp [hb hij]
  · intro i j
    rw [hφ]; simpa using h1 i j
  · intro i j
    rw [show (Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) α)⁻¹ =
      Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) α⁻¹ from (map_inv _ _).symm, hφ]
    show φ (φ.symm ((α⁻¹).1 i j)) ∈ O'
    rw [RingEquiv.apply_symm_apply]
    exact h2 i j
  · rw [← map_mul, ← e, hinv]

def pairM {R₁ R₂ : Type} {r : ℕ} (x : Matrix (Fin r) (Fin r) R₁) (y : Matrix (Fin r) (Fin r) R₂) :
    Matrix (Fin r) (Fin r) (R₁ × R₂) := Matrix.of fun i j => (x i j, y i j)

theorem pairM_mul {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {r : ℕ} (x x' : Matrix (Fin r) (Fin r) R₁)
    (y y' : Matrix (Fin r) (Fin r) R₂) : pairM (x * x') (y * y') = pairM x y * pairM x' y' := by
  ext i j
  · simp [pairM, Matrix.mul_apply, Prod.fst_sum]
  · simp [pairM, Matrix.mul_apply, Prod.snd_sum]

theorem pairM_one {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {r : ℕ} :
    pairM (1 : Matrix (Fin r) (Fin r) R₁) (1 : Matrix (Fin r) (Fin r) R₂) = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [pairM, Matrix.one_apply, h]

def pairGL {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {r : ℕ} (g₁ : GL (Fin r) R₁) (g₂ : GL (Fin r) R₂) :
    GL (Fin r) (R₁ × R₂) :=
  ⟨pairM g₁.1 g₂.1, pairM (g₁⁻¹).1 (g₂⁻¹).1, by rw [← pairM_mul, Units.mul_inv, Units.mul_inv, pairM_one],
    by rw [← pairM_mul, Units.inv_mul, Units.inv_mul, pairM_one]⟩

theorem hasIw_prod {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {O₁ : Subring R₁} {O₂ : Subring R₂}
    (h₁ : HasIw R₁ O₁) (h₂ : HasIw R₂ O₂) : HasIw (R₁ × R₂) (O₁.prod O₂) := by
  intro r β
  obtain ⟨b₁, α₁, hb₁, h1₁, h2₁, e₁⟩ := h₁ r (Matrix.GeneralLinearGroup.map (RingHom.fst R₁ R₂) β)
  obtain ⟨b₂, α₂, hb₂, h1₂, h2₂, e₂⟩ := h₂ r (Matrix.GeneralLinearGroup.map (RingHom.snd R₁ R₂) β)
  refine ⟨pairGL b₁ b₂, pairGL α₁ α₂, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Prod.ext (hb₁ hij) (hb₂ hij)
  · intro i j
    exact Subring.mem_prod.2 ⟨h1₁ i j, h1₂ i j⟩
  · intro i j
    exact Subring.mem_prod.2 ⟨h2₁ i j, h2₂ i j⟩
  · apply Units.ext
    rw [Units.val_mul]
    change β.1 = pairM b₁.1 b₂.1 * pairM α₁.1 α₂.1
    rw [← pairM_mul, ← Units.val_mul, ← Units.val_mul, ← e₁, ← e₂]
    ext i j <;> simp [pairM]

end GlobalTheory.LocIwasawaGL

namespace GlobalTheory.LocIwasawaGL

open scoped TensorProduct Matrix
open GlobalTheory.AdelicU GlobalTheory.LFun

theorem iwasawa_intLoc : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (r : ℕ)
    (β : GL (Fin r) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)),
    ∃ b α : GL (Fin r) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), b.1.BlockTriangular id ∧
      (∀ i j, α.1 i j ∈ intLoc D.host.F D.host.E v) ∧ (∀ i j, (α⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) ∧
      β = b * α := by
  intro D v r β
  suffices hI : HasIw (TensorProduct D.host.F (Fv D.host.F v) D.host.E) (intLoc D.host.F D.host.E v) from hI r β
  have := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have h : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPv.over.symm
  have hi := GlobalTheory.LPositivity.split_or_inert D w
  rw [h] at hi
  rcases hi with ⟨P₁, Q₁, hne, h₁, h₂⟩ | hw
  · obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) hne (HeightOneSpectrum.ext h₁)
      (HeightOneSpectrum.ext h₂)
    refine hasIw_of_equiv (splitAlgEquiv (isCMExt_host D) τ).toRingEquiv (fun y => ?_)
      (hasIw_prod (hasIw_valuationSubring (v.adicCompletionIntegers D.host.F))
        (hasIw_valuationSubring (v.adicCompletionIntegers D.host.F)))
    rw [mem_intLoc_iff_split (isCMExt_host D) τ, Subring.mem_prod]
    rfl
  · exact hasIw_of_equiv (InertChart.complEquiv hw h) (fun y => InertChart.mem_intLoc_iff hw h y)
      (hasIw_valuationSubring (w.adicCompletionIntegers D.host.E))

end GlobalTheory.LocIwasawaGL

end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_iwasawa_block_triangular : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (r : ℕ) (β : GL (Fin r) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), ∃ b α : GL (Fin r) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), b.1.BlockTriangular id ∧ (∀ i j, α.1 i j ∈ intLoc D.host.F D.host.E v) ∧ (∀ i j, (α⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) ∧ β = b * α := by
  atlas_forward_decl GlobalTheory.LocIwasawaGL.iwasawa_intLoc
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.LeviIntegral

open scoped Matrix TensorProduct
open Formalism.UG (cT hform)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (sigR inclR JR hR HR HA)

section Generic

variable {A : Type} [CommRing A] (s : A →+* A) {n r : ℕ}

theorem cT_add' {m p : Type} (X Y : Matrix m p A) : cT s (X + Y) = cT s X + cT s Y := by
  ext i j; simp [cT]

theorem cT_sub' {m p : Type} (X Y : Matrix m p A) : cT s (X - Y) = cT s X - cT s Y := by
  ext i j; simp [cT]

theorem cT_cT' (hs : ∀ x, s (s x) = x) {m p : Type} (X : Matrix m p A) : cT s (cT s X) = X := by
  ext i j; simp [cT, hs]

theorem cT_mul_mulVec_apply {k : Type} [Fintype k] (X : Matrix (Fin n) k A) (J : Matrix (Fin n) (Fin n) A)
    (y : Fin n → A) (i : k) : ((cT s X * J) *ᵥ y) i = hform s J (fun l => X l i) y := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, cT, hform, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

def frameLevi (J : Matrix (Fin n) (Fin n) A) (E0 F0 : Matrix (Fin n) (Fin r) A) (a b : Matrix (Fin r) (Fin r) A) :
    Matrix (Fin n) (Fin n) A :=
  1 + E0 * a * cT s F0 * J + F0 * b * cT s E0 * J

variable {s} {J : Matrix (Fin n) (Fin n) A} {E0 F0 : Matrix (Fin n) (Fin r) A}

theorem frameLevi_mul (hEE : cT s E0 * J * E0 = 0) (hFF : cT s F0 * J * F0 = 0) (hFE : cT s F0 * J * E0 = 1)
    (hEF : cT s E0 * J * F0 = 1) (a b a' b' : Matrix (Fin r) (Fin r) A) :
    frameLevi s J E0 F0 a b * frameLevi s J E0 F0 a' b' = frameLevi s J E0 F0 (a + a' + a * a') (b + b' + b * b') := by
  have e1 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s F0 * (J * (E0 * Z)) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFE, Matrix.one_mul]
  have e2 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s F0 * (J * (F0 * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFF, Matrix.zero_mul]
  have e3 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s E0 * (J * (E0 * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE, Matrix.zero_mul]
  have e4 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s E0 * (J * (F0 * Z)) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEF, Matrix.one_mul]
  simp only [frameLevi, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, e1, e2, e3, e4,
    Matrix.mul_zero, add_zero, zero_add]
  abel

theorem frameLevi_zero : frameLevi s J E0 F0 0 0 = 1 := by
  simp [frameLevi]

theorem frameLevi_mul_isotropic (hEE : cT s E0 * J * E0 = 0) (hFE : cT s F0 * J * E0 = 1) (a b : Matrix (Fin r) (Fin r) A) :
    frameLevi s J E0 F0 a b * E0 = E0 * (1 + a) := by
  have e1 : cT s F0 * (J * E0) = 1 := by rw [← Matrix.mul_assoc, hFE]
  have e3 : cT s E0 * (J * E0) = 0 := by rw [← Matrix.mul_assoc, hEE]
  simp only [frameLevi, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, e1, e3,
    Matrix.mul_zero, add_zero]

theorem frameLevi_unitary (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) (hEE : cT s E0 * J * E0 = 0)
    (hFF : cT s F0 * J * F0 = 0) (hFE : cT s F0 * J * E0 = 1) (hEF : cT s E0 * J * F0 = 1)
    {a b : Matrix (Fin r) (Fin r) A} (ha : a + cT s b + cT s b * a = 0) (hb : b + cT s a + cT s a * b = 0) :
    cT s (frameLevi s J E0 F0 a b) * J * frameLevi s J E0 F0 a b = J := by
  have e1 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s F0 * (J * (E0 * Z)) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFE, Matrix.one_mul]
  have e2 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s F0 * (J * (F0 * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFF, Matrix.zero_mul]
  have e3 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s E0 * (J * (E0 * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE, Matrix.zero_mul]
  have e4 : ∀ {k : Type} (Z : Matrix (Fin r) k A), cT s E0 * (J * (F0 * Z)) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEF, Matrix.one_mul]
  have key : J * (E0 * ((a + cT s b + cT s b * a) * (cT s F0 * J))) +
      J * (F0 * ((b + cT s a + cT s a * b) * (cT s E0 * J))) = 0 := by
    rw [ha, hb]; simp
  calc cT s (frameLevi s J E0 F0 a b) * J * frameLevi s J E0 F0 a b
      = J + (J * (E0 * ((a + cT s b + cT s b * a) * (cT s F0 * J))) +
          J * (F0 * ((b + cT s a + cT s a * b) * (cT s E0 * J)))) := by
        simp only [frameLevi, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_one, cT_cT' s hs, hJ, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, e1, e2, e3, e4, Matrix.mul_zero, add_zero, zero_add]
        abel
    _ = J := by rw [key, add_zero]

end Generic

end GlobalTheory.LeviIntegral

noncomputable section

namespace GlobalTheory.LeviIntegral

open scoped Matrix TensorProduct
open Formalism.UG (cT hform)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (sigR inclR JR hR HR HA)
open GlobalTheory.TruncKer

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

def frameMat (R : Type) [CommRing R] [Algebra F R] {k : ℕ} (x : Fin k → V.V) :
    Matrix (Fin V.rank) (Fin k) (R ⊗[F] E) :=
  Matrix.of fun y i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (x i) y

theorem sig_sig (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    sigR R hc.sig (sigR R hc.sig z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, CMData.sig]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem cT_JR (R : Type) [CommRing R] [Algebra F R] : cT (sigR R hc.sig) (JR R V.gram) = JR R V.gram := by
  have h := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_gram hc V
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at hij ⊢
  simp only [JR, Matrix.map_apply, inclR, sigR]
  rw [← hij]
  simp

theorem hform_coordR (R : Type) [CommRing R] [Algebra F R] (x y : V.V) :
    hform (sigR R hc.sig) (JR R V.gram) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R x) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R y) =
      inclR R (V.hT x y) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hform, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR, JR, inclR, sigR, CMData.sig, TensorProduct.tmul_sum, starRingEnd_apply]

theorem cT_frameMat_mul (R : Type) [CommRing R] [Algebra F R] {k l : ℕ} (x : Fin k → V.V) (y : Fin l → V.V) :
    cT (sigR R hc.sig) (frameMat (F := F) V R x) * JR (F := F) R V.gram * frameMat (F := F) V R y =
      Matrix.of fun i j => inclR R (V.hT (x i) (y j)) := by
  ext i j
  rw [Matrix.of_apply, ← hform_coordR hc V R]
  simp only [Matrix.mul_apply, cT, hform, Matrix.transpose_apply, Matrix.map_apply, frameMat, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end Frame

end GlobalTheory.LeviIntegral

end

noncomputable section

namespace GlobalTheory.LeviIntegral

open scoped Matrix TensorProduct
open Formalism.UG (cT hform)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (sigR inclR JR hR HR HA)
open GlobalTheory.TruncKer

section Wf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {V : HSpace E} (Φ : WittFrame V) (R : Type) [CommRing R] [Algebra F R]

theorem frame_ee : cT (sigR R hc.sig) (frameMat (F := F) V R Φ.e) * JR (F := F) R V.gram *
    frameMat (F := F) V R Φ.e = 0 := by
  rw [cT_frameMat_mul]
  ext i j
  rw [Matrix.of_apply, Matrix.zero_apply, show V.hT (Φ.e i) (Φ.e j) = 0 from Φ.ee j i, map_zero]

theorem frame_ff : cT (sigR R hc.sig) (frameMat (F := F) V R Φ.f) * JR (F := F) R V.gram *
    frameMat (F := F) V R Φ.f = 0 := by
  rw [cT_frameMat_mul]
  ext i j
  rw [Matrix.of_apply, Matrix.zero_apply, show V.hT (Φ.f i) (Φ.f j) = 0 from Φ.ff j i, map_zero]

theorem frame_fe : cT (sigR R hc.sig) (frameMat (F := F) V R Φ.f) * JR (F := F) R V.gram *
    frameMat (F := F) V R Φ.e = 1 := by
  rw [cT_frameMat_mul]
  ext i j
  rw [Matrix.of_apply, show V.hT (Φ.f i) (Φ.e j) = _ from Φ.ef j i, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem frame_ef : cT (sigR R hc.sig) (frameMat (F := F) V R Φ.e) * JR (F := F) R V.gram *
    frameMat (F := F) V R Φ.f = 1 := by
  have h := congrArg (cT (sigR R hc.sig)) (frame_fe hc Φ R)
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT' _ (sig_sig hc R), cT_JR, Formalism.UG.cT_one, ← Matrix.mul_assoc] at h
  exact h

end Wf

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {V : HSpace E} {L : Submodule (𝓞 E) (Fin V.rank → E)} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)}

theorem coordR_mem_latLoc {x : V.V} (hx : V.frame.equivFun x ∈ L) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V (Fv F v) x ∈ GlobalTheory.AdelicU.latLoc F L v := by
  have := GlobalTheory.AdelicU.tmul_mem_latLoc (F := F) (v := v) (one_mem (v.adicCompletionIntegers F)) hx
  convert this using 1
  funext i
  simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR, inclR]

theorem frameMat_mulVec_mem {k : ℕ} (x : Fin k → V.V) (hx : ∀ i, V.frame.equivFun (x i) ∈ L)
    (c : Fin k → Fv F v ⊗[F] E) (hcv : ∀ i, c i ∈ intLoc F E v) :
    frameMat (F := F) V (Fv F v) x *ᵥ c ∈ GlobalTheory.AdelicU.latLoc F L v := by
  have e : frameMat (F := F) V (Fv F v) x *ᵥ c =
      ∑ i, (⟨c i, hcv i⟩ : intLoc F E v) • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V (Fv F v) (x i) := by
    funext y
    simp [Matrix.mulVec, dotProduct, frameMat, Finset.sum_apply, Subring.smul_def, mul_comm]
  rw [e]
  exact sum_mem fun i _ => Submodule.smul_mem _ _ (coordR_mem_latLoc (hx i))

theorem coef_mem (hsd : IsSelfDualAt hc.sig V.gram L v) {k : ℕ} (x : Fin k → V.V)
    (hx : ∀ i, V.frame.equivFun (x i) ∈ L) {y : Fin V.rank → Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.AdelicU.latLoc F L v)
    (i : Fin k) :
    ((cT (sigR (Fv F v) hc.sig) (frameMat (F := F) V (Fv F v) x) * JR (F := F) (Fv F v) V.gram) *ᵥ y) i ∈
      intLoc F E v := by
  rw [cT_mul_mulVec_apply]
  have hy' : y ∈ dualLoc hc.sig V.gram L v := hsd ▸ hy
  exact hy' _ (coordR_mem_latLoc (hx i))

theorem mulVec_mem_intLoc {k l : ℕ} (a : Matrix (Fin k) (Fin l) (Fv F v ⊗[F] E)) (ha : ∀ i j, a i j ∈ intLoc F E v)
    (w : Fin l → Fv F v ⊗[F] E) (hw : ∀ j, w j ∈ intLoc F E v) (i : Fin k) : (a *ᵥ w) i ∈ intLoc F E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (ha i j) (hw j)

theorem sub_one_mem_intLoc {k : ℕ} (a : Matrix (Fin k) (Fin k) (Fv F v ⊗[F] E)) (ha : ∀ i j, a i j ∈ intLoc F E v)
    (i j : Fin k) : (a - 1) i j ∈ intLoc F E v := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  refine sub_mem (ha i j) ?_
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem levi_mulVec_mem (hsd : IsSelfDualAt hc.sig V.gram L v) (Φ : WittFrame V)
    (he : ∀ i, V.frame.equivFun (Φ.e i) ∈ L) (hf : ∀ i, V.frame.equivFun (Φ.f i) ∈ L)
    {a b : Matrix (Fin (wittIndex V)) (Fin (wittIndex V)) (Fv F v ⊗[F] E)} (ha : ∀ i j, a i j ∈ intLoc F E v)
    (hb : ∀ i j, b i j ∈ intLoc F E v) {y : Fin V.rank → Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.AdelicU.latLoc F L v) :
    frameLevi (sigR (Fv F v) hc.sig) (JR (F := F) (Fv F v) V.gram) (frameMat (F := F) V (Fv F v) Φ.e)
      (frameMat (F := F) V (Fv F v) Φ.f) a b *ᵥ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  set s := sigR (Fv F v) hc.sig
  set J := JR (F := F) (Fv F v) V.gram
  set E0 := frameMat (F := F) V (Fv F v) Φ.e
  set F0 := frameMat (F := F) V (Fv F v) Φ.f
  have e : frameLevi s J E0 F0 a b *ᵥ y =
      y + E0 *ᵥ (a *ᵥ ((cT s F0 * J) *ᵥ y)) + F0 *ᵥ (b *ᵥ ((cT s E0 * J) *ᵥ y)) := by
    simp only [frameLevi, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  refine add_mem (add_mem hy ?_) ?_
  · exact frameMat_mulVec_mem Φ.e he _ (mulVec_mem_intLoc a ha _ (coef_mem hc hsd Φ.f hf hy))
  · exact frameMat_mulVec_mem Φ.f hf _ (mulVec_mem_intLoc b hb _ (coef_mem hc hsd Φ.e he hy))

end Lat

end GlobalTheory.LeviIntegral

end

noncomputable section

namespace GlobalTheory.LeviIntegral

open scoped Matrix TensorProduct
open Formalism.UG (cT hform)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (sigR inclR JR hR HR HA)
open GlobalTheory.TruncKer

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_mem_stabLoc_mul_frame (hc : CMData F E) {V : HSpace E} (Φ : WittFrame V)
    (L : Submodule (𝓞 E) (Fin V.rank → E)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hsd : GlobalTheory.AdelicU.IsSelfDualAt hc.sig V.gram L v)
    (he : ∀ i, V.frame.equivFun (Φ.e i) ∈ L) (hf : ∀ i, V.frame.equivFun (Φ.f i) ∈ L)
    (α : GL (Fin (wittIndex V)) (Fv F v ⊗[F] E)) (hα : ∀ i j, α.1 i j ∈ intLoc F E v)
    (hα' : ∀ i j, (α⁻¹).1 i j ∈ intLoc F E v) :
    ∃ m : GlobalTheory.AdelicU.GLoc hc.sig V.gram v, m ∈ GlobalTheory.AdelicU.stabLoc hc.sig V.gram L v ∧
      (HA.mat (F := F) (Fv F v) hc.sig V.gram m).1 * frameMat (F := F) V (Fv F v) Φ.e =
        frameMat (F := F) V (Fv F v) Φ.e * α.1 := by
  set s := sigR (Fv F v) hc.sig
  set J := JR (F := F) (Fv F v) V.gram
  set E0 := frameMat (F := F) V (Fv F v) Φ.e
  set F0 := frameMat (F := F) V (Fv F v) Φ.f
  have hs : ∀ z, s (s z) = z := sig_sig hc (Fv F v)
  have hJ : cT s J = J := cT_JR hc V (Fv F v)
  have hEE : cT s E0 * J * E0 = 0 := frame_ee hc Φ (Fv F v)
  have hFF : cT s F0 * J * F0 = 0 := frame_ff hc Φ (Fv F v)
  have hFE : cT s F0 * J * E0 = 1 := frame_fe hc Φ (Fv F v)
  have hEF : cT s E0 * J * F0 = 1 := frame_ef hc Φ (Fv F v)
  let Mof : GL (Fin (wittIndex V)) (Fv F v ⊗[F] E) → Matrix (Fin V.rank) (Fin V.rank) (Fv F v ⊗[F] E) :=
    fun X => frameLevi s J E0 F0 (X.1 - 1) (cT s (X⁻¹).1 - 1)
  have hmul : ∀ X, Mof X * Mof X⁻¹ = 1 := by
    intro X
    simp only [Mof]
    rw [frameLevi_mul hEE hFF hFE hEF, inv_inv]
    have h1 : X.1 - 1 + ((X⁻¹).1 - 1) + (X.1 - 1) * ((X⁻¹).1 - 1) = 0 := by
      have : X.1 - 1 + ((X⁻¹).1 - 1) + (X.1 - 1) * ((X⁻¹).1 - 1) = X.1 * (X⁻¹).1 - 1 := by noncomm_ring
      rw [this, Units.mul_inv, sub_self]
    have h2 : cT s (X⁻¹).1 - 1 + (cT s X.1 - 1) + (cT s (X⁻¹).1 - 1) * (cT s X.1 - 1) = 0 := by
      have : cT s (X⁻¹).1 - 1 + (cT s X.1 - 1) + (cT s (X⁻¹).1 - 1) * (cT s X.1 - 1) =
          cT s (X⁻¹).1 * cT s X.1 - 1 := by noncomm_ring
      rw [this, ← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one, sub_self]
    rw [h1, h2, frameLevi_zero]
  have hmul' : Mof α⁻¹ * Mof α = 1 := by
    have := hmul α⁻¹
    rwa [inv_inv] at this
  have hunit : cT s (Mof α) * J * Mof α = J := by
    refine frameLevi_unitary hs hJ hEE hFF hFE hEF ?_ ?_
    · rw [cT_sub', cT_cT' s hs, Formalism.UG.cT_one]
      have : α.1 - 1 + ((α⁻¹).1 - 1) + ((α⁻¹).1 - 1) * (α.1 - 1) = (α⁻¹).1 * α.1 - 1 := by noncomm_ring
      rw [this, Units.inv_mul, sub_self]
    · rw [cT_sub', Formalism.UG.cT_one]
      have : cT s (α⁻¹).1 - 1 + (cT s α.1 - 1) + (cT s α.1 - 1) * (cT s (α⁻¹).1 - 1) =
          cT s α.1 * cT s (α⁻¹).1 - 1 := by noncomm_ring
      rw [this, ← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one, sub_self]
  have hstab : ∀ X : GL (Fin (wittIndex V)) (Fv F v ⊗[F] E), (∀ i j, X.1 i j ∈ intLoc F E v) →
      (∀ i j, (X⁻¹).1 i j ∈ intLoc F E v) → ∀ y, y ∈ GlobalTheory.AdelicU.latLoc F L v →
        Mof X *ᵥ y ∈ GlobalTheory.AdelicU.latLoc F L v := fun X hX hX' y hy =>
    levi_mulVec_mem hc hsd Φ he hf (sub_one_mem_intLoc _ hX)
      (sub_one_mem_intLoc _ fun i j => GlobalTheory.AdelicU.sigR_mem_intLoc hc.sig (hX' j i)) hy
  let u : GL (Fin V.rank) (Fv F v ⊗[F] E) := ⟨Mof α, Mof α⁻¹, hmul α, hmul'⟩
  have hu : u ∈ HR (Fv F v) hc.sig V.gram := hunit
  let m : GlobalTheory.AdelicU.GLoc hc.sig V.gram v := (⟨u, hu⟩ : HR (Fv F v) hc.sig V.gram)
  refine ⟨m, ?_, ?_⟩
  · rw [GlobalTheory.AdelicU.mem_stabLoc]
    intro y
    change y ∈ _ ↔ Mof α *ᵥ y ∈ _
    constructor
    · exact hstab α hα hα' y
    · intro hy
      have := hstab α⁻¹ hα' (by rw [inv_inv]; exact hα) _ hy
      rwa [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec] at this
  · change Mof α * E0 = E0 * α.1
    simp only [Mof]
    rw [frameLevi_mul_isotropic hEE hFE, add_sub_cancel]

end Main

end GlobalTheory.LeviIntegral

end

namespace GlobalTheory.LeviIntegral

theorem exists_stabLoc_mul_frame_of_isGood : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), (∀ i j, α.1 i j ∈ intLoc D.host.F D.host.E v) → (∀ i j, (α⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) → ∃ m : GLoc D.sp.cm.sig V.gram v, m ∈ stabLoc D.sp.cm.sig V.gram L v ∧ (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram m).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * α.1 := by
  intro D V Φ L a hgood v α hα hα'
  exact exists_mem_stabLoc_mul_frame D.sp.cm Φ L v (hgood.2.1 v) (fun i => (hgood.2.2.1 i).1)
    (fun i => (hgood.2.2.1 i).2) α hα hα'

end GlobalTheory.LeviIntegral
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_levi_element_exists : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), (∀ i j, α.1 i j ∈ intLoc D.host.F D.host.E v) → (∀ i j, (α⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) → ∃ m : GLoc D.sp.cm.sig V.gram v, m ∈ stabLoc D.sp.cm.sig V.gram L v ∧ (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram m).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * α.1 := by
  atlas_forward_decl GlobalTheory.LeviIntegral.exists_stabLoc_mul_frame_of_isGood
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

open scoped TensorProduct

namespace GlobalTheory.IwasawaTri

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (coordR extSub act)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E} {R : Type} [CommRing R] [Algebra F R]

theorem act_mem_of_mem_span {S : Set V.V} {A : Submodule E V.V} {g : HA R hc.sig V.gram}
    (h : ∀ x ∈ S, act hc V g (coordR V R x) ∈ extSub (F := F) V R A) {x : V.V}
    (hx : x ∈ Submodule.span E S) : act hc V g (coordR V R x) ∈ extSub (F := F) V R A := by
  let f : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] Fin V.rank → R ⊗[F] E :=
    (HA.mat R hc.sig V.gram g).1.mulVecLin
  change f (coordR V R x) ∈ _
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [show coordR V R 0 = 0 from funext fun _ => by simp [coordR], map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 =>
    rw [show coordR V R (x + y) = coordR V R x + coordR V R y from funext fun _ => by simp [coordR], map_add]
    exact add_mem h1 h2
  | smul a x _ h1 =>
    rw [show coordR V R (a • x) = inclR (F := F) R a • coordR V R x from funext fun _ => by simp [coordR], map_smul]
    exact Submodule.smul_mem _ _ h1

end Gen

theorem mem_pLoc_flag0_of_mul_eq_upper : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (v : HeightOneSpectrum (𝓞 D.host.F)) (p : GLoc D.sp.cm.sig V.gram v) (b : Matrix (Fin (wittIndex V)) (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), b.BlockTriangular id → (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram p).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * b → p ∈ PLoc Φ.flag0 v := by
  intro D V Φ v p b hb h
  refine IsoFlag.mem_par.2 fun i => GlobalTheory.Cusp.mem_parab.2 fun x hx => ?_
  have hgen : ∀ j : Fin (wittIndex V), j.val < i.val →
      act D.sp.cm V p (coordR V (Fv D.host.F v) (Φ.e j)) ∈ extSub (F := D.host.F) V (Fv D.host.F v) (Φ.flag0.X i) := by
    intro j hj
    have hcol : act D.sp.cm V p (coordR V (Fv D.host.F v) (Φ.e j)) =
        ∑ k, b k j • coordR V (Fv D.host.F v) (Φ.e k) := by
      funext a
      have := congrFun (congrFun h a) j
      simp only [Matrix.mul_apply, Matrix.of_apply] at this
      simp only [act, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hcol]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : j < k
    · rw [hb hk, zero_smul]; exact zero_mem _
    · exact Submodule.smul_mem _ _ (GlobalTheory.Cusp.coordR_mem V _
        (Submodule.subset_span ⟨k, show k.val < i.val from Nat.lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hk)) hj, rfl⟩))
  exact act_mem_of_mem_span (S := Φ.e '' {j | j.val < i.val}) (fun _ ⟨j, hj, e⟩ => e ▸ hgen j hj) hx

end GlobalTheory.IwasawaTri
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_matrix_coordinates_triangular : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (v : HeightOneSpectrum (𝓞 D.host.F)) (p : GLoc D.sp.cm.sig V.gram v) (b : Matrix (Fin (wittIndex V)) (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), b.BlockTriangular id → (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram p).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * b → p ∈ PLoc Φ.flag0 v := by
  atlas_forward_decl GlobalTheory.IwasawaTri.mem_pLoc_flag0_of_mul_eq_upper
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.IwFinFlag

theorem matrix_map_ringHom_add_smul_sandwich {n r : Type} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r] {A : Type} [CommRing A]
    (P Q Mi M : Matrix n n A) (X : Matrix n r A) (β b α αi : Matrix r r A) (hP : P = Q * Mi) (hβ : Q * X = X * β)
    (hba : β = b * α) (hm : M * X = X * α) (N : Matrix n n A) (hN : N = Mi * M) (e1 : N = 1) (hα : α * αi = 1) :
    P * X = X * b := by
  have hinv : Mi * X = X * αi := by
    calc Mi * X = Mi * X * (α * αi) := by rw [hα, Matrix.mul_one]
      _ = Mi * (M * X) * αi := by rw [hm]; simp only [Matrix.mul_assoc]
      _ = X * αi := by rw [← Matrix.mul_assoc, ← hN, e1, Matrix.one_mul]
  rw [hP, Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hβ, hba, Matrix.mul_assoc, Matrix.mul_assoc, hα, Matrix.mul_one]

theorem mat_mul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : HA R σ J) :
    (HA.mat R σ J (x * y)).1 = (HA.mat R σ J x).1 * (HA.mat R σ J y).1 := rfl

theorem mat_one {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : (HA.mat R σ J 1).1 = 1 := rfl

set_option maxHeartbeats 1000000 in

theorem iwasawa_minPar_fin : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ v (g : GLoc D.sp.cm.sig V.gram v), ∃ p ∈ PLoc Φ.flag0 v, ∃ k ∈ stabLoc D.sp.cm.sig V.gram L v, g = p * k := by
  intro D V Φ L a hG v g
  rcases (em (Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v)).elim (GlobalTheory.T.local_decomposition_split_place D V Φ L a hG v · g)
    (GlobalTheory.T.local_decomposition_nonsplit_place D V Φ L a hG v · g) with ⟨q, k, hk, rfl, β, hβ⟩
  obtain ⟨b, α, hb, hα, hα', rfl⟩ := GlobalTheory.T.local_iwasawa_block_triangular D v (wittIndex V) β
  obtain ⟨m, hm, hmα⟩ := GlobalTheory.T.integral_levi_element_exists D V Φ L a hG v α hα hα'
  have hg : q * k = (q * m⁻¹) * (m * k) := by rw [mul_assoc, inv_mul_cancel_left]
  have e1 : (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram (m⁻¹ * m)).1 = 1 := by rw [inv_mul_cancel]; exact mat_one _ _ _
  exact ⟨q * m⁻¹, GlobalTheory.T.parabolic_matrix_coordinates_triangular D V Φ v (q * m⁻¹) b.1 hb (matrix_map_ringHom_add_smul_sandwich _ _ _ _ _ _ b.1 α.1 (α⁻¹).1 (mat_mul _ _ _ _ _) hβ
    (Units.val_mul b α) hmα _ (mat_mul _ _ _ _ _) e1 α.mul_inv), m * k, mul_mem hm hk, hg⟩

end GlobalTheory.IwFinFlag

end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_iwasawa_decomposition : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ v (g : GLoc D.sp.cm.sig V.gram v), ∃ p ∈ PLoc Φ.flag0 v, ∃ k ∈ stabLoc D.sp.cm.sig V.gram L v, g = p * k := by
  atlas_forward_decl GlobalTheory.IwFinFlag.iwasawa_minPar_fin
end

section
section
noncomputable section

namespace GlobalTheory.IwArchMin

open Matrix

section Alg

variable {A : Type} [CommRing A] {n : ℕ}

def toC (e : A ≃+* ℂ) (b : GL (Fin n) A) : (Fin n → A) →ₛₗ[(e : A →+* ℂ)] (Fin n → ℂ) where
  toFun y := fun r => e (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) r)
  map_add' y z := by funext r; simp [Matrix.mulVec_add]
  map_smul' c y := by funext r; simp [Matrix.mulVec_smul]

theorem toC_apply (e : A ≃+* ℂ) (b : GL (Fin n) A) (y : Fin n → A) (r : Fin n) :
    toC e b y r = e (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) r) := rfl

theorem inv_mul_val (b : GL (Fin n) A) : b.1 * (b⁻¹ : GL (Fin n) A).1 = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem toC_injective (e : A ≃+* ℂ) (b : GL (Fin n) A) : Function.Injective (toC e b) := by
  intro y z h
  have h1 : (b⁻¹ : GL (Fin n) A).1 *ᵥ y = (b⁻¹ : GL (Fin n) A).1 *ᵥ z :=
    funext fun r => e.injective (congrFun h r)
  have h2 := congrArg (fun v => b.1 *ᵥ v) h1
  simpa only [Matrix.mulVec_mulVec, inv_mul_val, Matrix.one_mulVec] using h2

theorem toC_mulVec (e : A ≃+* ℂ) (b M : GL (Fin n) A) (y : Fin n → A) :
    toC e b (M.1 *ᵥ y) =
      (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * M * b)).1 *ᵥ toC e b y := by
  funext r
  rw [toC_apply]
  have : (b⁻¹ : GL (Fin n) A).1 *ᵥ (M.1 *ᵥ y) = (b⁻¹ * M * b).1 *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ y) := by
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, inv_mul_val, Matrix.mul_one]
  rw [this]
  exact RingHom.map_mulVec (e : A →+* ℂ) _ _ r

theorem form_conj (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (b : GL (Fin n) A) (y z : Fin n → A) :
    (fun i => σ (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i)) ⬝ᵥ
      ((Formalism.UG.cT σ b.1 * J * b.1) *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ z)) = (fun i => σ (y i)) ⬝ᵥ (J *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, inv_mul_val, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 1
  funext i
  rw [Formalism.UG.cT, Matrix.vecMul_transpose]
  have := RingHom.map_mulVec σ b.1 ((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i
  rw [Matrix.mulVec_mulVec, inv_mul_val, Matrix.one_mulVec] at this
  exact this.symm

end Alg

end GlobalTheory.IwArchMin

namespace GlobalTheory.IwArchMin

open Matrix

section Alg2

variable {A : Type} [CommRing A] {n : ℕ}

theorem jm_eq_map (e : A ≃+* ℂ) (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε = (Matrix.diagonal fun i => if ε i then (1 : A) else -1).map (e : A →+* ℂ) := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_map (map_zero _)]
  congr 1; funext i; split_ifs <;> simp

theorem map_injective' (e : A ≃+* ℂ) {P Q : Matrix (Fin n) (Fin n) A} (h : P.map e = Q.map e) : P = Q := by
  ext i j; exact e.injective (congrFun (congrFun h i) j)

theorem exists_alg (σ : A →+* A) (e : A ≃+* ℂ) (he : ∀ x, e (σ x) = star (e x))
    (J : Matrix (Fin n) (Fin n) A) (b : GL (Fin n) A) (ε : Fin n → Bool)
    (S : Matrix (Fin n) (Fin n) A) (hSm : Formalism.REAL.Jm ε = S.map (e : A →+* ℂ)) (hb : Formalism.UG.cT σ b.1 * J * b.1 = S)
    {k : ℕ} (X : Fin (k + 1) → Submodule A (Fin n → A)) (h0 : X 0 = ⊥) (hX : Monotone X)
    (hiso : ∀ y ∈ X (Fin.last k), ∀ z ∈ X (Fin.last k), (fun i => σ (y i)) ⬝ᵥ (J *ᵥ z) = 0)
    (g : GL (Fin n) A) (hg : g ∈ Formalism.UG.UJ σ J) :
    ∃ K ∈ Formalism.UG.UJ σ J, b⁻¹ * K * b ∈ Formalism.UG.UJ σ 1 ∧ ∀ i, ∀ y ∈ X i, (g * K⁻¹).1 *ᵥ y ∈ X i := by
  have hJm := hSm
  let L := toC e b
  let W : Fin (k + 1) → Submodule ℂ (Fin n → ℂ) := fun i => (X i).map L
  have hWm : Monotone W := fun i j h => Submodule.map_mono (hX h)
  have hW : GlobalTheory.FlagMeas.IsIsoFlag ε
      (fun i : Fin k => Module.finrank ℂ (W i.succ) - Module.finrank ℂ (W i.castSucc)) W := by
    refine ⟨by simp [W, h0], hWm, fun i => ?_, ?_⟩
    · have := Submodule.finrank_mono (hWm (Fin.castSucc_le_succ i)); dsimp only; omega
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      have h1 : star (L y) = fun i => e (σ (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i)) := by
        funext i; simp [L, toC_apply, he]
      have h2 : Formalism.REAL.Jm ε *ᵥ L z = fun i => e ((S *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ z)) i) := by
        funext i; rw [hJm]; exact (RingHom.map_mulVec (e : A →+* ℂ) S _ i).symm
      rw [h1, h2]
      have h3 := (RingHom.map_dotProduct (e : A →+* ℂ) (fun i => σ (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i))
        (S *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ z))).symm
      refine h3.trans ?_
      rw [← hb, form_conj, hiso y hy z hz, map_zero]
  have mapForm : ∀ M : GL (Fin n) A, M ∈ Formalism.UG.UJ σ S →
      (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) M).1ᴴ * Formalism.REAL.Jm ε *
        (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) M).1 = Formalism.REAL.Jm ε := by
    intro M hM
    have hM' : Formalism.UG.cT σ M.1 * S * M.1 = S := hM
    change (M.1.map (e : A →+* ℂ))ᴴ * _ * M.1.map (e : A →+* ℂ) = _
    rw [← GlobalTheory.Core.Rk.IwArch.map_cT σ (e : A →+* ℂ) he, hJm, ← Matrix.map_mul, ← Matrix.map_mul, hM']
  have hg' : b⁻¹ * g * b ∈ Formalism.UG.UJ σ S := hb ▸ GlobalTheory.Core.Rk.IwArch.conj_mem_UJ σ b hg
  obtain ⟨kc, hkc, hstab⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW
    ⟨Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * g * b), mapForm _ hg'⟩
  set K0 := Matrix.GeneralLinearGroup.map (e.symm : ℂ →+* A) kc.1 with hK0
  have hK0e : Matrix.GeneralLinearGroup.map (e : A →+* ℂ) K0 = kc.1 := by
    ext i j; simp [K0]
  have hK0m : K0.1.map (e : A →+* ℂ) = kc.1.1 := congrArg Units.val hK0e
  have hkc2 : (kc.1.1)ᴴ * Formalism.REAL.Jm ε * kc.1.1 = Formalism.REAL.Jm ε := kc.2
  have hkc1 : (kc.1.1)ᴴ * kc.1.1 = 1 := hkc
  have hK0S : K0 ∈ Formalism.UG.UJ σ S := by
    show Formalism.UG.cT σ K0.1 * S * K0.1 = S
    apply map_injective' e
    have := hkc2
    rw [← hK0m, ← GlobalTheory.Core.Rk.IwArch.map_cT σ (e : A →+* ℂ) he, hJm, ← Matrix.map_mul, ← Matrix.map_mul] at this
    exact this
  have hK01 : K0 ∈ Formalism.UG.UJ σ 1 := by
    show Formalism.UG.cT σ K0.1 * 1 * K0.1 = 1
    apply map_injective' e
    have := hkc1
    rw [← hK0m, ← GlobalTheory.Core.Rk.IwArch.map_cT σ (e : A →+* ℂ) he, ← Matrix.map_mul] at this
    rw [Matrix.mul_one]
    refine this.trans ?_
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  refine ⟨b * K0 * b⁻¹, ?_, ?_, fun i y hy => ?_⟩
  · have := GlobalTheory.Core.Rk.IwArch.conj_mem_UJ σ b⁻¹ hK0S
    rw [inv_inv, ← hb, GlobalTheory.Core.Rk.IwArch.cT_inv_cancel] at this
    exact this
  · have : b⁻¹ * (b * K0 * b⁻¹) * b = K0 := by group
    rw [this]; exact hK01
  · have hy' : L y ∈ W i := Submodule.mem_map_of_mem hy
    have h4 := hstab i (L y) hy'
    have e1 : Formalism.MainNotions.S.uMat (⟨Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * g * b), mapForm _ hg'⟩ * kc⁻¹ :
        Formalism.REAL.UJ ε) = (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * (g * (b * K0 * b⁻¹)⁻¹) * b)).1 := by
      have : b⁻¹ * (g * (b * K0 * b⁻¹)⁻¹) * b = (b⁻¹ * g * b) * K0⁻¹ := by group
      have e2 : Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * (g * (b * K0 * b⁻¹)⁻¹) * b) =
          Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * g * b) * kc.1⁻¹ := by
        rw [this, map_mul (Matrix.GeneralLinearGroup.map (e : A →+* ℂ)) (b⁻¹ * g * b) K0⁻¹, map_inv, hK0e]
      rw [e2]; rfl
    rw [e1, ← toC_mulVec] at h4
    obtain ⟨z, hz, hzL⟩ := Submodule.mem_map.1 h4
    rwa [toC_injective e b hzL] at hz

end Alg2

end GlobalTheory.IwArchMin

namespace GlobalTheory.IwArchMin

open scoped TensorProduct
open NumberField Matrix

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_par_mul_stabArch (hc : Formalism.BasicNotions.CMData F E) (hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E hc.sig)
    (V : Formalism.BasicNotions.HSpace E) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (w : InfinitePlace F)
    (b : GL (Fin V.rank) (w.Completion ⊗[F] E)) (ε : Fin V.rank → Bool)
    (hb : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig) b.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion V.gram * b.1 =
      Matrix.diagonal fun i => if ε i then 1 else -1)
    (g : GlobalTheory.AdelicU.GArch hc.sig V.gram w) :
    ∃ p ∈ 𝔉.par hc w.Completion, ∃ k ∈ GlobalTheory.AdelicU.stabArch hc.sig V.gram w b, g = p * k := by
  obtain ⟨τ⟩ : Nonempty (GlobalTheory.AdelicU.EmbOver E w) := inferInstance
  let e : w.Completion ⊗[F] E ≃+* ℂ := RingEquiv.ofBijective (GlobalTheory.AdelicU.infEmb τ) (GlobalTheory.AdelicU.infEmb_bijective hcm τ)
  have he : ∀ x, e (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig x) = star (e x) := fun x =>
    (GlobalTheory.AdelicU.infEmb_sigR hcm τ x).symm
  let X : Fin (𝔉.k + 1) → Submodule (w.Completion ⊗[F] E) (Fin V.rank → w.Completion ⊗[F] E) :=
    fun i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub V w.Completion (𝔉.X i)
  have h0 : X 0 = ⊥ := by simp [X, 𝔉.zero]
  have hX : Monotone X := fun i j h => GlobalTheory.Cusp.extSub_mono V w.Completion (𝔉.strictMono.monotone h)
  have hiso : ∀ y ∈ X (Fin.last 𝔉.k), ∀ z ∈ X (Fin.last 𝔉.k),
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig (y i)) ⬝ᵥ
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion V.gram *ᵥ z) = 0 := by
    intro y hy z hz
    have hz' := GlobalTheory.Cusp.extSub_mono V w.Completion 𝔉.iso hz
    have := (GlobalTheory.Cusp.mem_extSub_perp hc V).1 hz' y hy
    rw [GlobalTheory.Cusp.hR_eq] at this
    exact this
  obtain ⟨K, hK, hK1, hp⟩ := exists_alg (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig) e he
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion V.gram) b ε _ (jm_eq_map e ε) hb X h0 hX hiso
    (GlobalTheory.AdelicU.matHom w.Completion hc.sig V.gram g) g.2
  let kk : GlobalTheory.AdelicU.GArch hc.sig V.gram w := ⟨K, hK⟩
  refine ⟨g * kk⁻¹, ?_, kk, GlobalTheory.AdelicU.mem_stabArch.2 hK1, by group⟩
  refine GlobalTheory.Cusp.IsoFlag.mem_par.2 fun i => GlobalTheory.Cusp.mem_parab_iff_maps.2 fun y hy => ?_
  have := hp i y hy
  exact this

end Place

end GlobalTheory.IwArchMin

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.IwArchMin

theorem iwasawa_minPar : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ w (g : GArch D.sp.cm.sig V.gram w), ∃ p ∈ PArch Φ.flag0 w,
      ∃ k ∈ stabArch D.sp.cm.sig V.gram w (Formalism.UG.bc (compInf D.host.F D.host.E w) a), g = p * k := by
  intro D V Φ L a h w g
  obtain ⟨ε, hε⟩ := h.2.2.2.1 w
  exact exists_par_mul_stabArch D.sp.cm (isCMExt_host D) _ Φ.flag0 w _ ε hε g

end GlobalTheory.IwArchMin
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_iwasawa_decomposition : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ w (g : GArch D.sp.cm.sig V.gram w), ∃ p ∈ PArch Φ.flag0 w, ∃ k ∈ stabArch D.sp.cm.sig V.gram w (Formalism.UG.bc (compInf D.host.F D.host.E w) a), g = p * k := by
  atlas_forward_decl GlobalTheory.IwArchMin.iwasawa_minPar
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.AdelicIwasawaGlue

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

open Classical in

theorem exists_arch_part (x : ∀ w : InfinitePlace F, GArch σ J w) (s : Finset (InfinitePlace F)) :
    ∃ q : GAd σ J, (∀ v, proj σ J v q = 1) ∧ ∀ w, projArch σ J w q = if w ∈ s then x w else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun v => map_one _, fun w => by simp⟩
  | insert w s hw ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨embArch σ J w (x w) * q, fun v => by simp [h1 v], fun u => ?_⟩
    by_cases e : u = w
    · subst e; simp [h2 u, hw]
    · rw [map_mul, projArch_embArch_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

open Classical in

theorem exists_fin_part (x : ∀ v : HeightOneSpectrum (𝓞 F), GLoc σ J v) (s : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ q : GAd σ J, (∀ w, projArch σ J w q = 1) ∧ ∀ v, proj σ J v q = if v ∈ s then x v else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun w => map_one _, fun v => by simp⟩
  | insert v s hv ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨emb σ J v (x v) * q, fun w => by simp [h1 w], fun u => ?_⟩
    by_cases e : u = v
    · subst e; simp [h2 u, hv]
    · rw [map_mul, proj_emb_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

end GlobalTheory.AdelicIwasawaGlue

namespace GlobalTheory.AdelicIwasawa

open GlobalTheory.AdelicU GlobalTheory.AdelicIwasawaGlue

theorem iwasawa : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ g : GA D V, ∃ p : PA Φ.flag0, ∃ k ∈ (levelAll D.sp.cm.sig V.gram L a), g = p * k := by
  classical
  intro D V Φ L a hG g
  haveI : Submodule.IsLattice _ L := hG.1
  choose pf hpf kf hkf hf using fun v => GlobalTheory.T.local_iwasawa_decomposition D V Φ L a hG v (proj _ _ v g)
  choose pa hpa ka hka ha using fun w => GlobalTheory.T.archimedean_iwasawa_decomposition D V Φ L a hG w (projArch _ _ w g)
  have hS := (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram L g)
  set S := (Filter.eventually_cofinite.1 hS).toFinset with hSdef
  obtain ⟨qa, qa1, qa2⟩ := exists_arch_part D.sp.cm.sig V.gram pa Finset.univ
  obtain ⟨qf, qf1, qf2⟩ := exists_fin_part D.sp.cm.sig V.gram pf S
  have hp : qa * qf ∈ PA Φ.flag0 := by
    refine GlobalTheory.Cusp.IsoFlag.mem_par_adelic.2 ⟨fun w => ?_, fun v => ?_⟩
    · rw [map_mul, qa2 w, qf1 w, mul_one, if_pos (Finset.mem_univ w)]; exact hpa w
    · rw [map_mul, qa1 v, qf2 v, one_mul]
      split_ifs
      · exact hpf v
      · exact one_mem _
  refine ⟨⟨qa * qf, hp⟩, (qa * qf)⁻¹ * g, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩, (mul_inv_cancel_left (qa * qf) g).symm⟩
  · rw [map_mul, map_inv, map_mul, qa1 v, qf2 v, one_mul]
    split_ifs with h
    · rw [hf v, inv_mul_cancel_left]; exact hkf v
    · rw [inv_one, one_mul]
      by_contra hc
      exact h ((Set.Finite.mem_toFinset _).2 hc)
  · rw [map_mul, map_inv, map_mul, qa2 w, qf1 w, mul_one, if_pos (Finset.mem_univ w), ha w, inv_mul_cancel_left]
    exact hka w

end GlobalTheory.AdelicIwasawa
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_adelic : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ g : GA D V, ∃ p : PA Φ.flag0, ∃ k ∈ (levelAll D.sp.cm.sig V.gram L a), g = p * k := by
  first | exact @GlobalTheory.AdelicIwasawa.iwasawa | exact GlobalTheory.AdelicIwasawa.iwasawa | (intros; apply GlobalTheory.AdelicIwasawa.iwasawa <;> assumption)
end
