import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSphericalNumberField
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEntryLeMRow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIntIndMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalSplitOfPointwise
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuadCharUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdChEOfOrdUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorHalfNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticUniformizerOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralSubst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrInertOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AddCharConductorInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerSphericalSpan
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedDiagonalAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBCBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RamifiedQuadraticExtensionUniformizer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticExtensionUniformizerValuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerMemSphericalSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilMaxCompactFixedVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedUnramifiedHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilInducedRepresentationHypothesisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GluePlaces

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SchurDual

open GroundTheory.Automorphic.Spherical

variable {n : ℕ}

noncomputable def negHom (n : ℕ) : LaurentRing n →ₐ[ℂ] LaurentRing n :=
  AddMonoidAlgebra.lift ℂ (LaurentRing n) (Fin n → ℤ)
    { toFun := fun l => monomial (-(Multiplicative.toAdd l))
      map_one' := by
        simp only [toAdd_one, neg_zero]
        rfl
      map_mul' := fun a b => by
        rw [toAdd_mul, neg_add, monomial_add] }

theorem negHom_monomial (μ : Fin n → ℤ) : negHom n (monomial μ) = monomial (-μ) := by
  rw [negHom, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem monomialChar_inv (l : Fin n → ℤ) (z : Fin n → ℂˣ) :
    monomialChar l (fun i => (z i)⁻¹) = monomialChar (-l) z := by
  simp only [monomialChar_apply, Pi.neg_apply, _root_.inv_zpow, _root_.zpow_neg]

theorem evalAt_inv (z : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt (fun i => (z i)⁻¹) p = evalAt z (negHom n p) := by
  have h : evalAt (fun i => (z i)⁻¹) = (evalAt z).comp (negHom n) := by
    refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
    rw [AlgHom.comp_apply, negHom_monomial, evalAt_single, evalAt_single, monomialChar_inv]
  rw [h, AlgHom.comp_apply]

theorem negHom_alternant (μ : Fin n → ℤ) : negHom n (alternant μ) = alternant (-μ) := by
  simp only [alternant, antisymm_apply, map_sum, Units.smul_def, map_zsmul, permAct_monomial,
    negHom_monomial]
  rfl

theorem alternant_comp_rev (μ : Fin n → ℤ) :
    alternant (μ ∘ Fin.rev) = Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) • alternant μ := by
  have h := antisymm_permAct (Fin.revPerm : Equiv.Perm (Fin n)) (monomial μ)
  rw [permAct_monomial] at h
  exact h

theorem neg_staircase_comp_rev :
    (-(staircase n)) ∘ Fin.rev = staircase n + fun _ => (1 - (n : ℤ)) := by
  funext i
  have hi := i.isLt
  simp only [Function.comp_apply, Pi.neg_apply, Pi.add_apply, staircase, Fin.val_rev]
  omega

theorem neg_add_staircase_comp_rev (l : Fin n → ℤ) :
    (-(l + staircase n)) ∘ Fin.rev =
      ((fun i => -l (Fin.rev i)) + staircase n) + fun _ => (1 - (n : ℤ)) := by
  funext i
  have hi := i.isLt
  simp only [Function.comp_apply, Pi.neg_apply, Pi.add_apply, staircase, Fin.val_rev]
  omega

theorem negHom_schur (l : Fin n → ℤ) :
    negHom n (schur l) = schur (fun i => -l (Fin.rev i)) := by
  have h1 : alternant (-(staircase n)) * negHom n (schur l) = alternant (-(l + staircase n)) := by
    rw [← negHom_alternant, ← negHom_alternant, ← map_mul, alternant_mul_schur]
  have h2 := congrArg (fun x => Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) • x) h1
  simp only [← smul_mul_assoc, ← alternant_comp_rev, neg_staircase_comp_rev,
    neg_add_staircase_comp_rev, alternant_add_const] at h2
  rw [← alternant_mul_schur, mul_assoc] at h2
  have hM : (monomial (fun _ => (1 - (n : ℤ))) : LaurentRing n) ≠ 0 := by
    intro h
    have h3 := congrArg (evalAt (fun _ : Fin n => (1 : ℂˣ))) h
    simp [evalAt_single, monomialChar_apply] at h3
  exact mul_left_cancel₀ alternant_staircase_ne_zero (mul_left_cancel₀ hM h2)

theorem evalAt_inv_schur (n : ℕ) (z : Fin n → ℂˣ) (l : Fin n → ℤ) :
    evalAt (fun i => (z i)⁻¹) (schur l) = evalAt z (schur (fun i => -l (Fin.rev i))) := by
  rw [evalAt_inv, negHom_schur]

end GlobalTheory.CompanionTheory.SchurDual
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_inverse_eq_reversed_neg : ∀ (n : ℕ) (z : Fin n → ℂˣ) (l : Fin n → ℤ), Spherical.evalAt (fun i => (z i)⁻¹) (Spherical.schur l) = Spherical.evalAt z (Spherical.schur (fun i => -l (Fin.rev i))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SchurDual.evalAt_inv_schur
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SphGL3

theorem antitone_triple_iff (a b : ℤ) : Antitone (![a, b, 0] : Fin 3 → ℤ) ↔ b ≤ a ∧ 0 ≤ b := by
  constructor
  · intro h
    exact ⟨by simpa using h (show (0 : Fin 3) ≤ 1 by decide),
      by simpa using h (show (1 : Fin 3) ≤ 2 by decide)⟩
  · rintro ⟨h1, h2⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega

theorem rhoPair_triple (a b : ℤ) : GroundTheory.Automorphic.Spherical.rhoPair (![a, b, 0] : Fin 3 → ℤ) = 2 * a := by
  simp [GroundTheory.Automorphic.Spherical.rhoPair, Fin.sum_univ_three]

theorem sph_dg_zpow : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ z (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * Spherical.evalAt z (Spherical.schur ![a, b, 0]) else 0 := by
  intro F _ _ _ _ ψ₀ hψ₀ z a b
  obtain ⟨k, hk, hdg⟩ := GlobalTheory.CompanionTheory.LocalUnramified.sDg F (unifUnit F ^ a) (unifUnit F ^ b) 1
  have o1 : ord (((unifUnit F ^ a : Fˣ)) : F) = a := ord_unifUnit_zpow a
  have o2 : ord (((unifUnit F ^ b : Fˣ)) : F) = b := ord_unifUnit_zpow b
  have o3 : ord (((1 : Fˣ)) : F) = 0 := by simp [ord]
  rw [o1, o2, o3] at hdg
  rw [hdg, Spherical.sphericalWhittaker_mul_right hψ₀ _ _ hk, Spherical.sphericalWhittaker_torusPow hψ₀]
  by_cases h : b ≤ a ∧ 0 ≤ b
  · have hsq2 : Spherical.sqrtQ F ^ 2 = (residueCard F : ℂ) := by
      rw [Spherical.sqrtQ_sq]
      rfl
    rw [if_pos ((antitone_triple_iff a b).2 h), if_pos h, Spherical.halfModulus_eq, rhoPair_triple,
      show -(2 * a) = (2 : ℤ) * (-a) by ring, _root_.zpow_mul, zpow_ofNat, hsq2]
  · rw [if_neg (fun h' => h ((antitone_triple_iff a b).1 h')), if_neg h]

end GlobalTheory.CompanionTheory.SphGL3
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_formula_GL3_diag : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ z (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * Spherical.evalAt z (Spherical.schur ![a, b, 0]) else 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SphGL3.sph_dg_zpow
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2Factorization.DualGauge

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem tinv_mul (g h : GL (Fin 3) F) : GL2LocalData.tinv (g * h) = GL2LocalData.tinv g * GL2LocalData.tinv h := by
  apply Units.ext
  show ((g * h)⁻¹ : GL (Fin 3) F).valᵀ = (g⁻¹ : GL (Fin 3) F).valᵀ * (h⁻¹ : GL (Fin 3) F).valᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

def tinvHom : GL (Fin 3) F →* GL (Fin 3) F := MonoidHom.mk' GL2LocalData.tinv tinv_mul

theorem weyl_transposeInv_diag_GL3 (x y z : Fˣ) :
    (GL2LocalData.w3 : GL (Fin 3) F) * GL2LocalData.tinv (dg x y z) = dg z⁻¹ y⁻¹ x⁻¹ * GL2LocalData.w3 := by
  apply Units.ext
  have e : ((dg x y z : GL (Fin 3) F)⁻¹ : GL (Fin 3) F).val = (dg x y z : GL (Fin 3) F).inv := rfl
  show (GL2LocalData.w3 : GL (Fin 3) F).val * ((dg x y z : GL (Fin 3) F)⁻¹ : GL (Fin 3) F).valᵀ = _
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, GL2LocalData.w3, Matrix.mul_apply, Fin.sum_univ_three]

theorem weyl_GL3_mem_integralGL : (GL2LocalData.w3 : GL (Fin 3) F) ∈ integralGL F 3 := by
  refine (GLnLocal.mem_integralGL_iff F 3).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [GL2LocalData.w3, zero_mem, one_mem]
  · have e : ((GL2LocalData.w3 : GL (Fin 3) F)⁻¹ : GL (Fin 3) F).val = (GL2LocalData.w3 : GL (Fin 3) F).inv := rfl
    show ((GL2LocalData.w3 : GL (Fin 3) F)⁻¹ : GL (Fin 3) F).val i j ∈ _
    rw [e]
    fin_cases i <;> fin_cases j <;> simp [GL2LocalData.w3, zero_mem, one_mem]

end Local

end GlobalTheory.CompanionTheory.GL2Factorization.DualGauge
end
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SphericalDual

theorem spherical_whittaker_long_weyl3_transpose_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ z (GL2LocalData.w3 * GL2LocalData.tinv (dg (unifUnit F ^ a) (unifUnit F ^ b) 1)) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * Spherical.evalAt z (Spherical.schur ![0, -b, -a]) else 0 := by
  intro F _ _ _ _ ψ₀ hψ₀ z a b
  borelize F
  obtain ⟨k, hk, hdg⟩ := GlobalTheory.CompanionTheory.LocalUnramified.sDg F 1 (unifUnit F ^ (-b)) (unifUnit F ^ (-a))
  have e1 : (GL2LocalData.w3 : GL (Fin 3) F) * GL2LocalData.tinv (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) =
      dg 1 (unifUnit F ^ (-b)) (unifUnit F ^ (-a)) * GL2LocalData.w3 := by
    rw [GlobalTheory.CompanionTheory.GL2Factorization.DualGauge.weyl_transposeInv_diag_GL3, inv_one, _root_.zpow_neg, _root_.zpow_neg]
  have o1 : ord (((1 : Fˣ)) : F) = 0 := by simp [ord]
  rw [ord_unifUnit_zpow, ord_unifUnit_zpow, o1] at hdg
  have hanti : Antitone (![0, -b, -a] : Fin 3 → ℤ) ↔ b ≤ a ∧ 0 ≤ b := by
    constructor
    · intro h
      have h1 := h (show (0 : Fin 3) ≤ 1 by decide)
      have h2 := h (show (1 : Fin 3) ≤ 2 by decide)
      simp at h1 h2
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩ i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
  have hrho : Spherical.rhoPair (![0, -b, -a] : Fin 3 → ℤ) = 2 * a := by
    simp [Spherical.rhoPair, Fin.sum_univ_three]
  have hq : Spherical.sqrtQ F ^ (-(2 * a)) = (residueCard F : ℂ) ^ (-a) := by
    rw [show -(2 * a) = 2 * (-a) by ring, _root_.zpow_mul, zpow_ofNat, Spherical.sqrtQ_sq]
    rfl
  rw [e1, hdg, mul_assoc, Spherical.sphericalWhittaker_mul_right hψ₀ z _
    (mul_mem hk GlobalTheory.CompanionTheory.GL2Factorization.DualGauge.weyl_GL3_mem_integralGL), Spherical.sphericalWhittaker_torusPow hψ₀ z]
  simp only [hanti]
  split_ifs with h
  · rw [Spherical.halfModulus_eq, hrho, hq]
  · rfl

end GlobalTheory.CompanionTheory.SphericalDual
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_formula_GL3_long_weyl_dual : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ z (GL2LocalData.w3 * GL2LocalData.tinv (dg (unifUnit F ^ a) (unifUnit F ^ b) 1)) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * Spherical.evalAt z (Spherical.schur ![0, -b, -a]) else 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SphericalDual.spherical_whittaker_long_weyl3_transpose_inv
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2Factorization.ZU.SphericalWhittakerGL2

theorem diag_uniformizer_eq_torus_mul_integral {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (a b : ℤ) :
    ∃ k ∈ GLnLocal.integralGL F 2, (d2 (unifUnit F ^ a) (unifUnit F ^ b) : GL (Fin 2) F) =
      Iwasawa.torusPow F 2 ![a, b] * k := by
  obtain ⟨u, hu⟩ := GlobalTheory.CompanionTheory.LocalUnramified.exists_unit_eq_uniformizer_zpow_ord_mul F (unifUnit F ^ a)
  obtain ⟨v, hv⟩ := GlobalTheory.CompanionTheory.LocalUnramified.exists_unit_eq_uniformizer_zpow_ord_mul F (unifUnit F ^ b)
  rw [ord_unifUnit_zpow] at hu hv
  refine ⟨GLnLocal.integralGLHom F 2 (d2 u v), ⟨_, rfl⟩, ?_⟩
  apply Units.ext
  ext i j
  rw [Units.val_mul, Iwasawa.coe_torusPow]
  fin_cases i <;> fin_cases j <;>
    simp [d2, GLnLocal.integralGLHom, Matrix.diagonal_mul, ← hu, ← hv]

theorem spherical_whittaker_GL2_uniformizer_diag : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (y : Fin 2 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ y (d2 (unifUnit F ^ a) (unifUnit F ^ b)) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * Spherical.evalAt y (Spherical.schur ![a, b]) else 0 := by
  intro F _ _ _ _ ψ₀ hψ₀ y a b
  obtain ⟨k, hk, hdg⟩ := diag_uniformizer_eq_torus_mul_integral (F := F) a b
  have hanti : Antitone (![a, b] : Fin 2 → ℤ) ↔ b ≤ a := by
    constructor
    · intro h
      simpa using h (show (0 : Fin 2) ≤ 1 by decide)
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have hrho : Spherical.rhoPair (![a, b] : Fin 2 → ℤ) = a - b := by
    simp [Spherical.rhoPair, Fin.sum_univ_two]
    ring
  rw [hdg, Spherical.sphericalWhittaker_mul_right hψ₀ _ _ hk,
    Spherical.sphericalWhittaker_torusPow hψ₀]
  by_cases h : b ≤ a
  · rw [if_pos (hanti.2 h), if_pos h, Spherical.halfModulus_eq, hrho]
  · rw [if_neg (fun h' => h (hanti.1 h')), if_neg h]

end GlobalTheory.CompanionTheory.GL2Factorization.ZU.SphericalWhittakerGL2
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_formula_GL2_diag : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (y : Fin 2 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ y (d2 (unifUnit F ^ a) (unifUnit F ^ b)) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * Spherical.evalAt y (Spherical.schur ![a, b]) else 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.ZU.SphericalWhittakerGL2.spherical_whittaker_GL2_uniformizer_diag
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.SphericalWhittakerDualGL2

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem transpose_inv_diagonal_two (p q : Fˣ) : GL2LocalData.tinv (d2 p q) = d2 p⁻¹ q⁻¹ := by
  apply Units.ext
  have hinv : (d2 p q)⁻¹ = d2 p⁻¹ q⁻¹ := by
    apply Units.ext
    rfl
  show ((d2 p q)⁻¹ : GL (Fin 2) F).val.transpose = (d2 p⁻¹ q⁻¹).val
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d2]

theorem long_weyl2_mul_diagonal_two (p q : Fˣ) : (GL2LocalData.w2 : GL (Fin 2) F) * d2 p q = d2 q p * GL2LocalData.w2 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d2, GL2LocalData.w2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_mem_integral : (GL2LocalData.w2 : GL (Fin 2) F) ∈ GLnLocal.integralGL F 2 := by
  refine (GLnLocal.mem_integralGL_iff F 2).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
  · show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]

theorem exists_unif_eq : ∃ e : 𝒪[F]ˣ, unifUnit F = Iwasawa.uniformizerUnit F * unitsIncl F e := by
  have hw : ord ((Iwasawa.uniformizerUnit F : Fˣ) : F) = 1 :=
    ord_uniformizer (GLnLocal.irreducible_uniformizer F)
  have hu : ord ((unifUnit F : Fˣ) : F) = 1 := by simpa using ord_unifUnit_zpow (K := F) 1
  have hmem : (Iwasawa.uniformizerUnit F)⁻¹ * unifUnit F ∈ (unitsIncl F).range := by
    rw [mem_range_unitsIncl_iff, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      normalizedValuation_eq_exp_ord (Units.ne_zero _), normalizedValuation_eq_exp_ord (Units.ne_zero _),
      hw, hu]
    exact inv_mul_cancel₀ (by simp)
  obtain ⟨e, he⟩ := hmem
  exact ⟨e, by rw [he]; group⟩

theorem diag_uniformizer_zpow_torus_integral (c d : ℤ) : ∃ k ∈ GLnLocal.integralGL F 2,
    d2 (unifUnit F ^ c) (unifUnit F ^ d) = Iwasawa.torusPow F 2 ![c, d] * k := by
  obtain ⟨e, he⟩ := exists_unif_eq (F := F)
  refine ⟨_, Iwasawa.diagGL_map_mem_integralGL F 2 ![e ^ c, e ^ d], ?_⟩
  apply Units.ext
  have hz : ∀ m : ℤ, ((unifUnit F ^ m : Fˣ) : F) =
      ((Iwasawa.uniformizerUnit F ^ m : Fˣ) : F) * ((unitsIncl F (e ^ m) : Fˣ) : F) := by
    intro m
    rw [he, mul_zpow, map_zpow, Units.val_mul]
  have hc : ∀ m : ℤ, (((e ^ m : 𝒪[F]ˣ) : 𝒪[F]) : F) = ((e : 𝒪[F]) : F) ^ m := by
    intro m
    have h := congrArg Units.val (map_zpow (unitsIncl F) e m)
    rw [Units.val_zpow_eq_zpow_val, coe_unitsIncl, coe_unitsIncl] at h
    exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d2, Iwasawa.torusPow, Iwasawa.diagGL, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hz, hc]

theorem antitone_iff (a b : ℤ) : Antitone (![-b, -a] : Fin 2 → ℤ) ↔ b ≤ a := by
  constructor
  · intro h
    have := h (show (0 : Fin 2) ≤ 1 by decide)
    simpa using this
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem rhoPair_pair (a b : ℤ) : Spherical.rhoPair (![-b, -a] : Fin 2 → ℤ) = a - b := by
  simp [Spherical.rhoPair, Fin.sum_univ_two]
  ring

theorem spherical_whittaker_long_weyl2_transpose_inv (ψ₀ : AddChar F ℂ) (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (y : Fin 2 → ℂˣ) (a b : ℤ) :
    Spherical.sphericalWhittaker ψ₀ y (GL2LocalData.w2 * GL2LocalData.tinv (d2 (unifUnit F ^ a) (unifUnit F ^ b))) =
      if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * Spherical.evalAt y (Spherical.schur ![-b, -a])
      else 0 := by
  obtain ⟨k, hk, hd⟩ := diag_uniformizer_zpow_torus_integral (F := F) (-b) (-a)
  rw [transpose_inv_diagonal_two, long_weyl2_mul_diagonal_two, ← _root_.zpow_neg, ← _root_.zpow_neg, hd,
    Spherical.sphericalWhittaker_mul_right hψ₀ y _ weyl_mem_integral,
    Spherical.sphericalWhittaker_mul_right hψ₀ y _ hk,
    Spherical.sphericalWhittaker_torusPow hψ₀, Spherical.halfModulus_eq, rhoPair_pair]
  simp only [antitone_iff]

end

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (y : Fin 2 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ y (GL2LocalData.w2 * GL2LocalData.tinv (d2 (unifUnit F ^ a) (unifUnit F ^ b))) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * Spherical.evalAt y (Spherical.schur ![-b, -a]) else 0 :=
  fun _ _ _ _ _ ψ₀ hψ₀ y a b => spherical_whittaker_long_weyl2_transpose_inv ψ₀ hψ₀ y a b

end GlobalTheory.CompanionTheory.GL2Factorization.SphericalWhittakerDualGL2
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_formula_GL2_long_weyl_dual : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (y : Fin 2 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ y (GL2LocalData.w2 * GL2LocalData.tinv (d2 (unifUnit F ^ a) (unifUnit F ^ b))) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * Spherical.evalAt y (Spherical.schur ![-b, -a]) else 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.SphericalWhittakerDualGL2.main
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.CauchyUnit

def antitonePairEquiv : ℕ × ℕ ≃ {l : Fin 2 → ℕ // Antitone l} where
  toFun p := ⟨![p.1 + p.2, p.2], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  invFun l := (l.1 0 - l.1 1, l.1 1)
  left_inv p := by simp
  right_inv l := by
    apply Subtype.ext
    have h : l.1 1 ≤ l.1 0 := l.2 (by simp)
    funext i
    fin_cases i
    · simp; omega
    · simp

theorem padN_pair (m n : ℕ) :
    (fun i : Fin 3 => ((PositivityTheory.RgJS.padN 3 (![m + n, n] : Fin 2 → ℕ) i : ℕ) : ℤ)) =
      ![((m + n : ℕ) : ℤ), (n : ℤ), 0] := by
  funext i
  fin_cases i <;> simp [PositivityTheory.RgJS.padN]

theorem pair_cast (m n : ℕ) :
    (fun j : Fin 2 => (((![m + n, n] : Fin 2 → ℕ) j : ℕ) : ℤ)) = ![((m + n : ℕ) : ℤ), (n : ℤ)] := by
  funext j
  fin_cases j <;> simp

theorem pair_sum (m n : ℕ) : ∑ j, (![m + n, n] : Fin 2 → ℕ) j = m + 2 * n := by
  simp [Fin.sum_univ_two]; omega

theorem cauchy_unit : ∀ (x : Fin 3 → ℂˣ) (y : Fin 2 → ℂˣ) (X : ℂ), (∀ i, ‖(x i : ℂ)‖ = 1) → (∀ j, ‖(y j : ℂ)‖ = 1) → ‖X‖ < 1 → HasSum (fun p : ℕ × ℕ => Spherical.evalAt x (Spherical.schur ![((p.1 + p.2 : ℕ) : ℤ), (p.2 : ℤ), 0]) * Spherical.evalAt y (Spherical.schur ![((p.1 + p.2 : ℕ) : ℤ), (p.2 : ℤ)]) * X ^ (p.1 + 2 * p.2)) (∏ i, ∏ j, (1 - (x i : ℂ) * (y j : ℂ) * X)⁻¹) := by
  intro x y X hx hy hX
  have h := (PositivityTheory.RgJS.cauchy_variation_inequality 3 2 (by norm_num) x y X 1 1
    (fun i => (hx i).le) (fun j => (hy j).le) (by simpa using hX)).2
  have h2 := (Equiv.hasSum_iff antitonePairEquiv).2 h
  convert h2 using 2 with p
  obtain ⟨m, n⟩ := p
  simp only [Function.comp_apply, antitonePairEquiv, Equiv.coe_fn_mk]
  rw [padN_pair, pair_cast, pair_sum]

end GlobalTheory.CompanionTheory.CauchyUnit
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchy_identity_schur_GL3_GL2 : ∀ (x : Fin 3 → ℂˣ) (y : Fin 2 → ℂˣ) (X : ℂ), (∀ i, ‖(x i : ℂ)‖ = 1) → (∀ j, ‖(y j : ℂ)‖ = 1) → ‖X‖ < 1 → HasSum (fun p : ℕ × ℕ => Spherical.evalAt x (Spherical.schur ![((p.1 + p.2 : ℕ) : ℤ), (p.2 : ℤ), 0]) * Spherical.evalAt y (Spherical.schur ![((p.1 + p.2 : ℕ) : ℤ), (p.2 : ℤ)]) * X ^ (p.1 + 2 * p.2)) (∏ i, ∏ j, (1 - (x i : ℂ) * (y j : ℂ) * X)⁻¹) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CauchyUnit.cauchy_unit
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.ZUSum

open scoped NNReal

theorem term_identity (q : ℕ) (hq : q ≠ 0) (r : ℂ) (hr : r = ((NNReal.sqrt (q : ℝ≥0) : ℝ) : ℂ))
    (s : ℂ) (m n : ℕ) :
    (q : ℂ) ^ (-((m : ℤ) + (n : ℤ))) * r ^ (-(m : ℤ)) * ((q : ℂ) ^ (-(m : ℂ) * (s - 3 / 2))) *
        ((q : ℂ) ^ (-(n : ℂ) * (2 * s - 1))) = ((q : ℂ) ^ (-s)) ^ (m + 2 * n) := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hr2 : r = Complex.exp (Complex.log (q : ℂ) / 2) := by
    have h1 : ((NNReal.sqrt (q : ℝ≥0) : ℝ)) = Real.exp (Real.log (q : ℝ) / 2) := by
      rw [Real.coe_sqrt, Real.exp_half, Real.exp_log hpos]
      simp
    rw [hr, h1, Complex.ofReal_exp, Complex.ofReal_div, Complex.natCast_log]
    simp
  have hqe : ∀ k : ℤ, (q : ℂ) ^ k = Complex.exp ((k : ℂ) * Complex.log (q : ℂ)) := by
    intro k
    rw [Complex.exp_int_mul, Complex.exp_log hq']
  rw [hr2, hqe, ← Complex.exp_int_mul, Complex.cpow_def_of_ne_zero hq', Complex.cpow_def_of_ne_zero hq',
    Complex.cpow_def_of_ne_zero hq', ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem zU_eq_of_hasSum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (S S' : ℤ → ℤ → ℂ) (s R : ℂ), (∀ a b : ℤ, W (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * S a b else 0) → (∀ a b : ℤ, W' (d2 (unifUnit F ^ a) (unifUnit F ^ b)) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * S' a b else 0) → HasSum (fun p : ℕ × ℕ => S ((p.1 + p.2 : ℕ) : ℤ) (p.2 : ℤ) * S' ((p.1 + p.2 : ℕ) : ℤ) (p.2 : ℤ) * ((residueCard F : ℂ) ^ (-s)) ^ (p.1 + 2 * p.2)) R → zU W W' s = R := by
  intro F _ _ _ _ W W' S S' s R hW hW' hS
  have hinj : Function.Injective (fun p : ℕ × ℕ => (((p.1 : ℤ), (p.2 : ℤ)) : ℤ × ℤ)) := by
    intro p p' h
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Prod.ext h.1 h.2
  unfold zU
  refine HasSum.tsum_eq ((hinj.hasSum_iff ?_).1 ?_)
  · intro p hp
    have hneg : ¬ (0 ≤ p.1 ∧ 0 ≤ p.2) := by
      rintro ⟨h1, h2⟩
      refine hp ⟨(p.1.toNat, p.2.toNat), ?_⟩
      simp [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
    have hc : ¬ (p.2 ≤ p.1 + p.2 ∧ 0 ≤ p.2) := by
      rintro ⟨h1, h2⟩
      exact hneg ⟨by omega, h2⟩
    rw [hW, if_neg hc]
    simp
  · convert hS using 2 with p
    obtain ⟨m, n⟩ := p
    have h1 : ((n : ℤ) ≤ (m : ℤ) + (n : ℤ) ∧ (0 : ℤ) ≤ (n : ℤ)) := by omega
    have h2 : (n : ℤ) ≤ (m : ℤ) + (n : ℤ) := by omega
    have hid := term_identity (residueCard F) GroundTheory.LocalField.residueCard_ne_zero (Spherical.sqrtQ F) rfl s m n
    have hsub : (m : ℤ) + (n : ℤ) - (n : ℤ) = (m : ℤ) := by ring
    simp only [Function.comp_apply]
    rw [hW, hW', if_pos h1, if_pos h2, hsub, ← hid]
    push_cast
    ring

end GlobalTheory.CompanionTheory.GL2Factorization.ZUSum
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_rankin_selberg_eq_L_factor : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (S S' : ℤ → ℤ → ℂ) (s R : ℂ), (∀ a b : ℤ, W (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * S a b else 0) → (∀ a b : ℤ, W' (d2 (unifUnit F ^ a) (unifUnit F ^ b)) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * S' a b else 0) → HasSum (fun p : ℕ × ℕ => S ((p.1 + p.2 : ℕ) : ℤ) (p.2 : ℤ) * S' ((p.1 + p.2 : ℕ) : ℤ) (p.2 : ℤ) * ((residueCard F : ℂ) ^ (-s)) ^ (p.1 + 2 * p.2)) R → zU W W' s = R := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.ZUSum.zU_eq_of_hasSum
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.UnramifiedZeta

theorem norm_cpow_lt_one (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (s : ℂ) (hs : 0 < s.re) : ‖(residueCard F : ℂ) ^ (-s)‖ < 1 := by
  have hq : (1 : ℝ) < residueCard F := by exact_mod_cast GroundTheory.LocalField.one_lt_residueCard
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero GroundTheory.LocalField.residueCard_ne_zero)]
  exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simpa using hs)

theorem psi_trivial (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ψ : AddChar F Circle) (hψ : IsStd ψ) :
    (∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ) x = 1) ∧
      (∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ⁻¹) x = 1) := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  have key : ∀ x ∈ 𝒪[F], ψ x = 1 := fun x hx => ht x (mem_valBall_zero_iff.2 hx)
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · show ((ψ x : Circle) : ℂ) = 1
    rw [key x hx, Circle.coe_one]
  · show (((ψ⁻¹) x : Circle) : ℂ) = 1
    rw [AddChar.inv_apply, key (-x) (neg_mem hx), Circle.coe_one]

theorem unramified_sum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → IsUnramifiedChar ν → ∀ y : Fin 2 → ℂˣ, (∀ j, ‖((y j : ℂˣ) : ℂ)‖ = 1) → ∀ W' : GL (Fin 2) F → ℂ, (∀ g, W' g = Spherical.sphericalWhittaker (Circle.coeHom.compAddChar ψ⁻¹) y g) → ∀ s : ℂ, 0 < s.re → zU (sphW ψ ν) W' s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![ν (unifUnit F), 1, (ν (unifUnit F))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * ((y j : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ ∧ zU (GL2LocalData.dW3 (sphW ψ ν)) (GL2LocalData.dW2 W') s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![ν (unifUnit F), 1, (ν (unifUnit F))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((y j)⁻¹ : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ := by
  intro F _ _ _ _ _ _ ψ hψ ν hν _ y hy W' hW' s hs
  obtain ⟨h1, h2⟩ := psi_trivial F ψ hψ
  have hW : W' = Spherical.sphericalWhittaker (Circle.coeHom.compAddChar ψ⁻¹) y := funext hW'
  subst hW
  set x : Fin 3 → ℂˣ := ![ν (unifUnit F), 1, (ν (unifUnit F))⁻¹] with hx
  have hα : ‖((ν (unifUnit F) : ℂˣ) : ℂ)‖ = 1 := hν.2 _
  have hxn : ∀ i, ‖(x i : ℂ)‖ = 1 := by
    intro i; fin_cases i <;> simp [hx, hα]
  have hxi : ∀ i, ‖(((x i)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    intro i; rw [Units.val_inv_eq_inv_val, norm_inv, hxn, inv_one]
  have hyi : ∀ j, ‖(((y j)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    intro j; rw [Units.val_inv_eq_inv_val, norm_inv, hy, inv_one]
  have hq := norm_cpow_lt_one F s hs
  constructor
  · refine GlobalTheory.T.unramified_rankin_selberg_eq_L_factor F (sphW ψ ν) _ (fun a b => Spherical.evalAt x (Spherical.schur ![a, b, 0]))
      (fun a b => Spherical.evalAt y (Spherical.schur ![a, b])) s _
      (fun a b => GlobalTheory.T.shintani_formula_GL3_diag F _ h1 x a b) (fun a b => GlobalTheory.T.shintani_formula_GL2_diag F _ h2 y a b) ?_
    exact GlobalTheory.T.cauchy_identity_schur_GL3_GL2 x y _ hxn hy hq
  · have key := GlobalTheory.T.cauchy_identity_schur_GL3_GL2 (fun i => (x i)⁻¹) (fun j => (y j)⁻¹) _ hxi hyi hq
    have hp : (∏ i, ∏ j, (1 - (((x i)⁻¹ : ℂˣ) : ℂ) * (((y j)⁻¹ : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹) =
        ∏ i, ∏ j, (1 - (x i : ℂ) * (((y j)⁻¹ : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ := by
      simp only [Fin.prod_univ_three, hx]
      simp
      ring
    rw [hp] at key
    refine GlobalTheory.T.unramified_rankin_selberg_eq_L_factor F _ _ (fun a b => Spherical.evalAt x (Spherical.schur ![0, -b, -a]))
      (fun a b => Spherical.evalAt y (Spherical.schur ![-b, -a])) s _
      (fun a b => GlobalTheory.T.shintani_formula_GL3_long_weyl_dual F _ h1 x a b) (fun a b => GlobalTheory.T.shintani_formula_GL2_long_weyl_dual F _ h2 y a b) ?_
    have e3 : ∀ a b : ℤ, Spherical.evalAt x (Spherical.schur ![0, -b, -a]) =
        Spherical.evalAt (fun i => (x i)⁻¹) (Spherical.schur ![a, b, 0]) := by
      intro a b
      rw [GlobalTheory.T.schur_inverse_eq_reversed_neg]
      congr 2
      funext i; fin_cases i <;> simp
    have e2 : ∀ a b : ℤ, Spherical.evalAt y (Spherical.schur ![-b, -a]) =
        Spherical.evalAt (fun i => (y i)⁻¹) (Spherical.schur ![a, b]) := by
      intro a b
      rw [GlobalTheory.T.schur_inverse_eq_reversed_neg]
      congr 2
      funext i; fin_cases i <;> simp
    simpa only [e3, e2] using key

end GlobalTheory.CompanionTheory.UnramifiedZeta
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitPrime

variable {K : Type} [Field K] [NumberField K]
open GlobalTheory.CompanionTheory.SphTheta

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unr_mul {a b : Fˣ →* ℂˣ} (ha : IsUnramifiedChar a) (hb : IsUnramifiedChar b) :
    IsUnramifiedChar (a * b) := fun u hu => by
  have h1 : a u = 1 := MonoidHom.mem_ker.mp (ha hu)
  have h2 : b u = 1 := MonoidHom.mem_ker.mp (hb hu)
  exact MonoidHom.mem_ker.mpr (by simp [h1, h2])

theorem unr_inv {a : Fˣ →* ℂˣ} (ha : IsUnramifiedChar a) : IsUnramifiedChar a⁻¹ := fun u hu => by
  have h1 : a u = 1 := MonoidHom.mem_ker.mp (ha hu)
  exact MonoidHom.mem_ker.mpr (by simp [h1])

end Local

theorem places_of_two (h2 : Module.finrank ℚ K = 2) (v : Pl) (w₁ w₂ : PlK K)
    [h₁ : w₁.asIdeal.LiesOver v.asIdeal] [h₂ : w₂.asIdeal.LiesOver v.asIdeal] (hne : w₁ ≠ w₂) :
    (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → w = w₁ ∨ w = w₂) ∧
    ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 ℚ) * w.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := by
  classical
  have hs := SemiLocal.sum_ramificationIdx_mul_inertiaDeg K v
  rw [h2] at hs
  set G : SemiLocal.PlacesOver K v → ℕ :=
    fun x => x.1.asIdeal.ramificationIdx (𝓞 ℚ) * x.1.asIdeal.inertiaDeg (𝓞 ℚ) with hG
  have hpos : ∀ x, 1 ≤ G x := fun x => by
    have h := finrank_adicCompletion v x.1
    have h3 : 0 < Module.finrank (v.adicCompletion ℚ) (x.1.adicCompletion K) := Module.finrank_pos
    rw [h] at h3
    exact h3
  set a : SemiLocal.PlacesOver K v := ⟨w₁, h₁⟩ with ha
  set b : SemiLocal.PlacesOver K v := ⟨w₂, h₂⟩ with hb
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  have hsum : ∑ x ∈ Finset.univ \ {a, b}, G x + (G a + G b) = 2 := by
    rw [← Finset.sum_pair hab, Finset.sum_sdiff (Finset.subset_univ _)]
    exact hs
  have ha1 := hpos a
  have hb1 := hpos b
  have hmem : ∀ x : SemiLocal.PlacesOver K v, x = a ∨ x = b := fun x => by
    by_contra hx
    have hx' : x ∈ Finset.univ \ ({a, b} : Finset (SemiLocal.PlacesOver K v)) := by
      simpa using hx
    have h4 := Finset.single_le_sum (f := G) (fun _ _ => Nat.zero_le _) hx'
    have h5 := hpos x
    omega
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rcases hmem ⟨w, hw⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · have h6 : G a = 1 := by omega
    have h7 : G b = 1 := by omega
    rcases hmem ⟨w, hw⟩ with h | h
    · have : G ⟨w, hw⟩ = 1 := h ▸ h6
      exact this
    · have : G ⟨w, hw⟩ = 1 := h ▸ h7
      exact this

section Place

variable (v : Pl) (w : PlK K) [hw : w.asIdeal.LiesOver v.asIdeal]

abbrev iota : (Qv v)ˣ →* (Kv K w)ˣ := Units.map (algebraMap (Qv v) (Kv K w)).toMonoidHom

theorem nrm_iota (hd : Module.finrank (Qv v) (Kv K w) = 1) (a : (Qv v)ˣ) :
    nrm v w (iota v w a) = a := by
  apply Units.ext
  show Algebra.norm (Qv v) (algebraMap (Qv v) (Kv K w) (a : Qv v)) = a
  rw [Algebra.norm_algebraMap, hd, pow_one]

theorem ord_iota (he : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) :
    ord ((iota v w (unifUnit (Qv v)) : (Kv K w)ˣ) : Kv K w) = 1 := by
  have hx : algebraMap (Qv v) (Kv K w) (unifUnit (Qv v) : Qv v) ≠ 0 := by simp
  have h1 := valued_algebraMap_adicCompletion v w (unifUnit (Qv v) : Qv v)
  rw [he, pow_one, valued_eq_exp_neg_ord hx, valued_eq_exp_neg_ord (Units.ne_zero _),
    ord_unifUnit] at h1
  exact neg_injective (WithZero.exp_injective h1)

theorem residueCard_eq (hf : w.asIdeal.inertiaDeg (𝓞 ℚ) = 1) :
    residueCard (Kv K w) = residueCard (Qv v) := by
  rw [residueCard_adicCompletion, residueCard_adicCompletion,
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg, hf, pow_one]

theorem localLFactor_place (he : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 ℚ) = 1) {μ : (Kv K w)ˣ →* ℂˣ} (hμ : IsUnramifiedChar μ) (s : ℂ) :
    localLFactor μ s =
      (1 - ((μ (iota v w (unifUnit (Qv v))) : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactor_of_isUnramified hμ, quasiChar_apply_eq_of_isUnramified hμ (ord_iota v w he),
    residueCard_eq v w hf]

theorem local_L_factor_split_place (D : Dat) (DK : DatK K) (hBC : IsBC D DK) (hv : v ∉ D.bad)
    (hd : Module.finrank (Qv v) (Kv K w) = 1) (he : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 ℚ) = 1) {C : (Kv K w)ˣ →* ℂˣ} (hC : IsUnramifiedChar C) (s : ℂ) :
    lf3 (DK.ν w) C s = ∏ i : Fin 3,
      (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) *
        ((C (iota v w (unifUnit (Qv v))) : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  have hν : IsUnramifiedChar (DK.ν w) := by
    rw [hBC.nu v w]
    exact GlobalTheory.CompanionTheory.BaseChangeData.isUnramifiedChar_comp_nrm v w (D.unr v hv)
  have hval : DK.ν w (iota v w (unifUnit (Qv v))) = D.ν v (unifUnit (Qv v)) := by
    rw [hBC.nu v w, MonoidHom.comp_apply, nrm_iota v w hd]
  unfold lf3
  rw [localLFactor_place v w he hf (unr_mul hν hC), localLFactor_place v w he hf hC,
    localLFactor_place v w he hf (unr_mul (unr_inv hν) hC), Fin.prod_univ_three]
  simp [MonoidHom.mul_apply, MonoidHom.inv_apply, hval]

theorem isUnit1_cAt (c : HeckeCharacter K) : IsUnit1 (cAt c v w) := by
  refine ⟨(GodementSection.continuous_localChar c w).comp
    (Continuous.units_map _ (_root_.continuous_algebraMap (Qv v) (Kv K w))), fun x => ?_⟩
  show ‖((localChar c w _ : ℂˣ) : ℂ)‖ = 1
  rw [GodementSection.coe_localChar]
  exact Circle.norm_coe _

end Place

theorem localChar_inv (c : HeckeCharacter K) (w : PlK K) :
    localChar c⁻¹ w = (localChar c w)⁻¹ := by
  have h1 := GodementSection.localChar_mul_inv (1 : HeckeCharacter K) c w
  have h2 := GodementSection.localChar_mul_inv c c w
  rw [mul_inv_cancel, mul_inv_cancel] at h2
  rw [one_mul, h2, one_mul] at h1
  exact h1

theorem finprod_places (v : Pl) (w₁ w₂ : PlK K) (h₁ : w₁.asIdeal.LiesOver v.asIdeal)
    (h₂ : w₂.asIdeal.LiesOver v.asIdeal) (hne : w₁ ≠ w₂)
    (hall : ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → w = w₁ ∨ w = w₂)
    (f : {w : PlK K // w.asIdeal.LiesOver v.asIdeal} → ℂ) :
    ∏ᶠ w, f w = f ⟨w₁, h₁⟩ * f ⟨w₂, h₂⟩ := by
  classical
  have hab : (⟨w₁, h₁⟩ : {w : PlK K // w.asIdeal.LiesOver v.asIdeal}) ≠ ⟨w₂, h₂⟩ :=
    fun h => hne (congrArg Subtype.val h)
  rw [finprod_eq_prod_of_mulSupport_subset f (s := {⟨w₁, h₁⟩, ⟨w₂, h₂⟩}),
    Finset.prod_pair hab]
  intro x _
  rcases hall x.1 x.2 with h | h
  · exact Finset.mem_coe.2 (Finset.mem_insert.2 (Or.inl (Subtype.ext h)))
  · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_singleton.2 (Subtype.ext h)))

theorem split_lfV : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (D : Dat) (DK : DatK K), IsBC D DK → ∀ (c : HeckeCharacter K) (v : Pl), v ∉ D.bad → (∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedChar (localChar c w) ∧ w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) → ∀ (w₁ w₂ : PlK K) [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal], w₁ ≠ w₂ → IsUnit1 (cAt c v w₁) ∧ IsUnit1 (cAt c v w₂) ∧ IsUnramifiedChar (cAt c v w₁) ∧ IsUnramifiedChar (cAt c v w₂) ∧ ∀ s : ℂ, lfV DK c v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((![cAt c v w₁ (unifUnit (Qv v)), cAt c v w₂ (unifUnit (Qv v))] : Fin 2 → ℂˣ) j : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ ∧ lfV DK c⁻¹ v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * ((((![cAt c v w₁ (unifUnit (Qv v)), cAt c v w₂ (unifUnit (Qv v))] : Fin 2 → ℂˣ) j)⁻¹ : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  intro K _ _ h2 D DK hBC c v hv hc w₁ w₂ h₁ h₂ hne
  obtain ⟨hall, hef⟩ := places_of_two h2 v w₁ w₂ hne
  have he : ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], w.asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    fun w _ => (hc w).2
  have hf : ∀ (w : PlK K) [hw : w.asIdeal.LiesOver v.asIdeal], w.asIdeal.inertiaDeg (𝓞 ℚ) = 1 :=
    fun w hw => Nat.eq_one_of_mul_eq_one_left (hef w hw)
  have hd : ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], Module.finrank (Qv v) (Kv K w) = 1 :=
    fun w _ => by rw [finrank_adicCompletion v w, he w, hf w, one_mul]
  have hcu : ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedChar (cAt c v w) :=
    fun w _ => GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w) _ (hc w).1
  refine ⟨isUnit1_cAt v w₁ c, isUnit1_cAt v w₂ c, hcu w₁, hcu w₂, fun s => ⟨?_, ?_⟩⟩
  · unfold lfV
    rw [finprod_places v w₁ w₂ h₁ h₂ hne hall]
    simp only [Fin.prod_univ_two, Finset.prod_mul_distrib]
    rw [local_L_factor_split_place v w₁ D DK hBC hv (hd w₁) (he w₁) (hf w₁) (hc w₁).1,
      local_L_factor_split_place v w₂ D DK hBC hv (hd w₂) (he w₂) (hf w₂) (hc w₂).1]
    rfl
  · unfold lfV
    rw [finprod_places v w₁ w₂ h₁ h₂ hne hall]
    simp only [Fin.prod_univ_two, Finset.prod_mul_distrib, localChar_inv]
    rw [local_L_factor_split_place v w₁ D DK hBC hv (hd w₁) (he w₁) (hf w₁) (unr_inv (hc w₁).1),
      local_L_factor_split_place v w₂ D DK hBC hv (hd w₂) (he w₂) (hf w₂) (unr_inv (hc w₂).1)]
    rfl

end GlobalTheory.CompanionTheory.SplitPrime
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.InertFactor

theorem inv_factor (a b Q : ℂ) :
    (1 - a ^ 2 * b ^ 2 * Q ^ 2)⁻¹ = (1 - a * b * Q)⁻¹ * (1 - a * (-b) * Q)⁻¹ := by
  rw [← mul_inv]
  congr 1
  ring

theorem cpow_sq (q : ℕ) (s : ℂ) : (((q ^ 2 : ℕ) : ℂ)) ^ (-s) = ((q : ℂ) ^ (-s)) ^ 2 := by
  rw [pow_two, pow_two, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

section Loc

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

theorem unr_mul {μ μ' : Eˣ →* ℂˣ} (h : IsUnramifiedChar μ) (h' : IsUnramifiedChar μ') :
    IsUnramifiedChar (μ * μ') :=
  isUnramifiedChar_iff.mpr fun u hu => by
    rw [MonoidHom.mul_apply, isUnramifiedChar_iff.mp h u hu, isUnramifiedChar_iff.mp h' u hu, one_mul]

theorem unr_inv {μ : Eˣ →* ℂˣ} (h : IsUnramifiedChar μ) : IsUnramifiedChar μ⁻¹ :=
  isUnramifiedChar_iff.mpr fun u hu => by
    rw [MonoidHom.inv_apply, isUnramifiedChar_iff.mp h u hu, inv_one]

theorem local_l_factor_rank_three_unramified (ν χ : Eˣ →* ℂˣ) (hν : IsUnramifiedChar ν) (hχ : IsUnramifiedChar χ) (A B : ℂˣ)
    (h1 : ν (unifUnit E) = A ^ 2) (h2 : χ (unifUnit E) = B ^ 2) (q : ℕ)
    (hq : residueCard E = q ^ 2) (s : ℂ) :
    lf3 ν χ s = ∏ i : Fin 3, ∏ j : Fin 2,
      (1 - ((![A, 1, A⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((![B, -B] : Fin 2 → ℂˣ) j : ℂˣ) : ℂ) *
        (q : ℂ) ^ (-s))⁻¹ := by
  unfold lf3
  rw [localLFactor_of_isUnramified (unr_mul hν hχ), localLFactor_of_isUnramified hχ,
    localLFactor_of_isUnramified (unr_mul (unr_inv hν) hχ), hq, cpow_sq]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, Fin.prod_univ_three,
    Fin.prod_univ_two]
  have e1 := inv_factor (A : ℂ) (B : ℂ) ((q : ℂ) ^ (-s))
  have e2 := inv_factor (1 : ℂ) (B : ℂ) ((q : ℂ) ^ (-s))
  have e3 := inv_factor ((A : ℂ)⁻¹) (B : ℂ) ((q : ℂ) ^ (-s))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, Units.val_neg, Units.val_one, inv_pow, one_pow, one_mul] at e1 e2 e3 ⊢
  rw [e1, e2, e3]

end Loc

variable {K : Type} [Field K] [NumberField K]

theorem localChar_one (c : HeckeCharacter K) (w : PlK K) : localChar (1 : HeckeCharacter K) w = 1 := by
  have := GroundTheory.Automorphic.GodementSection.localChar_mul_inv c c w
  rwa [mul_inv_cancel, mul_inv_cancel] at this

theorem localChar_inv (c : HeckeCharacter K) (w : PlK K) : localChar c⁻¹ w = (localChar c w)⁻¹ := by
  have := GroundTheory.Automorphic.GodementSection.localChar_mul_inv 1 c w
  rwa [one_mul, localChar_one c, one_mul] at this

theorem absNorm_over (v : Pl) (w : PlK K) [hw : w.asIdeal.LiesOver v.asIdeal] :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ w.asIdeal.inertiaDeg (𝓞 ℚ) := by
  rw [Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal]

theorem lfV_inert : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (D : Dat) (DK : DatK K), IsBC D DK → ∀ (c : HeckeCharacter K) (v : Pl), v ∉ D.bad → (∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedChar (localChar c w) ∧ w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) → ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], (∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) → Module.finrank (Qv v) (Kv K w) = 2 ∧ residueCard (Kv K w) = residueCard (Qv v) ^ 2 ∧ ∀ b : ℂˣ, b ^ 2 = localChar c w (Units.map (algebraMap (Qv v) (Kv K w)).toMonoidHom (unifUnit (Qv v))) → ∀ s : ℂ, lfV DK c v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((![b, -b] : Fin 2 → ℂˣ) j : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ ∧ lfV DK c⁻¹ v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * ((((![b, -b] : Fin 2 → ℂˣ) j)⁻¹ : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  intro K _ _ h2 D DK hBC c v hv hun w _ huniq
  rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w' _ => (hun w').2) with
    ⟨w₁, w₂, h₁, h₂, hne⟩ | ⟨w', hw', -, hfin, hord⟩
  · exact absurd ((huniq w₁ h₁).trans (huniq w₂ h₂).symm) hne
  obtain rfl := huniq w' hw'
  have hf : w'.asIdeal.inertiaDeg (𝓞 ℚ) = 2 := by
    have h := finrank_adicCompletion v w'
    rw [hfin, (hun w').2, one_mul] at h
    exact h.symm
  have hq : residueCard (Kv K w') = residueCard (Qv v) ^ 2 := by
    rw [residueCard_adicCompletion, residueCard_adicCompletion, absNorm_over v w', hf]
  refine ⟨hfin, hq, fun b hb s => ?_⟩
  set π : (Kv K w')ˣ := Units.map (algebraMap (Qv v) (Kv K w')).toMonoidHom (unifUnit (Qv v)) with hπdef
  have hπ : ord ((π : (Kv K w')ˣ) : Kv K w') = 1 := hord
  have hχu := (hun w').1
  have hνu : IsUnramifiedChar (DK.ν w') := DK.unr w' fun hbad => by
    rcases (hBC.bad v w').mp hbad with h | h
    · exact hv h
    · exact h (hun w').2
  have hχ : localChar c w' (unifUnit (Kv K w')) = b ^ 2 := by
    rw [← quasiChar_apply_eq_of_isUnramified hχu hπ, hb]
  have hnorm : nrm v w' π = unifUnit (Qv v) ^ 2 := by
    apply Units.ext
    simp [nrm, π, Algebra.norm_algebraMap, hfin]
  have hν : DK.ν w' (unifUnit (Kv K w')) = D.ν v (unifUnit (Qv v)) ^ 2 := by
    rw [← quasiChar_apply_eq_of_isUnramified hνu hπ, hBC.nu v w', MonoidHom.comp_apply, hnorm, map_pow]
  have hfib : GlobalTheory.CompanionTheory.PlaceBlocks.fib K v = {w'} := by
    ext x
    rw [GlobalTheory.CompanionTheory.PlaceBlocks.mem_fib, Finset.mem_singleton, ← GlobalTheory.CompanionTheory.PlaceBlocks.liesOver_iff]
    exact ⟨huniq x, fun h => h ▸ hw'⟩
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.PlaceBlocks.lfV_eq, hfib, Finset.prod_singleton]
    exact local_l_factor_rank_three_unramified _ _ hνu hχu _ _ hν hχ _ hq s
  · rw [GlobalTheory.CompanionTheory.PlaceBlocks.lfV_eq, hfib, Finset.prod_singleton, localChar_inv]
    rw [local_l_factor_rank_three_unramified (DK.ν w') (localChar c w')⁻¹ hνu (unr_inv hχu) (D.ν v (unifUnit (Qv v))) b⁻¹ hν
      (by rw [MonoidHom.inv_apply, hχ, inv_pow]) _ hq s]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    fin_cases j <;> simp

end GlobalTheory.CompanionTheory.InertFactor
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitStandardVector

theorem isUnit1_localChar {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (w : PlK K) :
    IsUnit1 (localChar c w) := by
  refine ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => ?_⟩
  rw [GroundTheory.Automorphic.GodementSection.coe_localChar]
  exact Circle.norm_coe _

theorem exists_sqrt_unit (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) : ∃ b : ℂˣ, b ^ 2 = a ∧ ‖(b : ℂ)‖ = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) (n := 2) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hz.symm)
  refine ⟨Units.mk0 z hz0, Units.ext (by simpa using hz), ?_⟩
  have h2 : ‖z‖ ^ 2 = 1 := by rw [← norm_pow, hz, ha]
  have h0 : 0 ≤ ‖z‖ := norm_nonneg z
  simpa using (pow_eq_one_iff_of_nonneg h0 (by norm_num)).1 h2

section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem indicator_eq_phiS :
    Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} (1 : F × F → ℂ) = phiS := by
  funext x
  by_cases h1 : x.1 ∈ 𝒪[F]
  · by_cases h2 : x.2 ∈ 𝒪[F]
    · rw [Set.indicator_of_mem (show x ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from ⟨h1, h2⟩)]
      simp [phiS, intInd_of_mem h1, intInd_of_mem h2]
    · rw [Set.indicator_of_notMem (fun h => h2 h.2)]
      simp [phiS, intInd_of_notMem h2]
  · rw [Set.indicator_of_notMem (fun h => h1 h.1)]
    simp [phiS, intInd_of_notMem h1]

theorem sphN_WcS_phiS (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (hχ : Ad3.IsStd χ)
    (hc₁ : IsUnramifiedChar c₁) (hc₂ : IsUnramifiedChar c₂) : SphN (GL2LocalData.WcS χ c₁ c₂ phiS) := by
  have H1 := GlobalTheory.CompanionTheory.SphTheta.SplitRW.rW_phiS F χ hχ
  have H2 := RowIwasawa.iwasawa_lower_row F
  have key : ∀ g : GL (Fin 2) F, GL2LocalData.WcS χ c₁ c₂ phiS g =
      ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det g) (1 / 2) *
        ((((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * (χ (xRow g) : ℂ) *
          ∫ u, sphJ c₁ c₂ (g.val).det (mRow g) u ∂multHaar F) := by
    intro g
    unfold GL2LocalData.WcS
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [H1 g u, sphJ]
    ring
  refine ⟨?_, ?_⟩
  · intro k hk g
    obtain ⟨hm, hD, hM, hx⟩ := H2 g k hk
    have hk1 : modulus (k.val).det = 1 := by
      have := (H2 1 k hk).2.1
      simpa using this
    have hdet : Matrix.GeneralLinearGroup.det (g * k) =
        Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det k := map_mul _ _ _
    have hc : ((c₁ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ) =
        ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
      rw [hdet, map_mul, Units.val_mul, char_eq_one hc₁ (u := Matrix.GeneralLinearGroup.det k) hk1, mul_one]
    have hmp : mp (Matrix.GeneralLinearGroup.det (g * k)) (1 / 2) =
        mp (Matrix.GeneralLinearGroup.det g) (1 / 2) := by
      unfold mp
      have : modulus ((Matrix.GeneralLinearGroup.det (g * k) : Fˣ) : F) =
          modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := hD
      rw [this]
    rw [key, key, hc, hmp, hM, sphJ_congr c₁ c₂ hD hM]
    by_cases hle : modulus (g.val).det ≤ modulus (mRow g) ^ 2
    · have ht := hx hle
      have h1 : χ (xRow (g * k) - xRow g) = 1 := by
        have h := isTrivialOn_addCharConductor hχ.1 hχ.2.1
        rw [hχ.2.2] at h
        exact h _ (mem_valBall_zero_iff.2 ht)
      have h2 : χ (xRow (g * k)) = χ (xRow g) := by
        have e : xRow (g * k) = (xRow (g * k) - xRow g) + xRow g := by ring
        rw [e, AddChar.map_add_eq_mul, h1, one_mul]
      rw [h2]
    · have h0 : (fun u => sphJ c₁ c₂ (g.val).det (mRow g) u) = fun _ => 0 :=
        funext (sphJ_eq_zero c₁ c₂ hm hle)
      simp only [h0, integral_zero, mul_zero]
  · rw [key]
    have hm1 : mRow (1 : GL (Fin 2) F) = 1 := by
      simp [mRow]
    have hx1 : xRow (1 : GL (Fin 2) F) = 0 := by
      simp [xRow]
    have hJ : (fun u => sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u) =
        (unitFiltrationUnits F 0 : Set Fˣ).indicator (fun _ => (1 : ℂ)) := by
      funext u
      by_cases hu : u ∈ (unitFiltrationUnits F 0 : Set Fˣ)
      · have hu1 : modulus (u : F) = 1 := mem_units_iff_modulus.1 hu
        rw [Set.indicator_of_mem hu]
        have e1 : ((c₂ u)⁻¹ : ℂˣ) = 1 := by
          have : c₂ u = 1 := hc₂ (mem_units_iff_modulus.2 hu1)
          rw [this, inv_one]
        unfold sphJ
        rw [e1, char_eq_one hc₁ hu1, intInd_of_mem, intInd_of_mem]
        · simp
        · rw [← modulus_le_one_iff]; simp [modulus_mul, hu1]
        · rw [← modulus_le_one_iff]; simp [modulus_mul, modulus_inv, hu1]
      · rw [Set.indicator_of_notMem hu]
        have hu1 : modulus (u : F) ≠ 1 := fun h => hu (mem_units_iff_modulus.2 h)
        unfold sphJ
        rcases lt_or_gt_of_ne hu1 with h | h
        · rw [intInd_of_notMem (x := (1 * (u : F))⁻¹)]
          · simp
          · rw [← modulus_le_one_iff, one_mul, modulus_inv, not_le]
            exact (one_lt_inv₀ (modulus_pos u.ne_zero)).2 h
        · rw [intInd_of_notMem (x := ((1 : GL (Fin 2) F).val).det * u / 1)]
          · simp
          · rw [← modulus_le_one_iff, not_le]
            simpa using h
    have hmeas : MeasurableSet (unitFiltrationUnits F 0 : Set Fˣ) := by
      exact (isOpen_unitFiltrationUnits 0).measurableSet
    have hint : ∫ u, sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u ∂multHaar F = 1 := by
      rw [hJ, integral_indicator_const _ hmeas]
      simp [Measure.real, multHaar_unitFiltrationUnits_zero]
    rw [hm1, hx1, hint]
    simp [mp]

theorem WcS_std_eq (χ : AddChar F Circle) (hχ : Ad3.IsStd χ) (c₁ c₂ : Fˣ →* ℂˣ) (u₁ : IsUnit1 c₁)
    (u₂ : IsUnit1 c₂) (r₁ : IsUnramifiedChar c₁) (r₂ : IsUnramifiedChar c₂) (g : GL (Fin 2) F) :
    GL2LocalData.WcS χ c₁ c₂ (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1) g =
      Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ)
        ![c₁ (unifUnit F), c₂ (unifUnit F)] g := by
  rw [indicator_eq_phiS]
  obtain ⟨-, h1, h2⟩ := GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial F χ hχ
  have hs := sphN_WcS_phiS χ c₁ c₂ hχ r₁ r₂
  have hm := GlobalTheory.T.compact_whittaker_mem_spherical_span F χ hχ c₁ c₂ u₁ u₂ r₁ r₂ phiS isLocallyConstant_phiS
    hasCompactSupport_phiS
  have := GlobalTheory.CompanionTheory.SphericalSpan.eq_mul_sphericalWhittaker F 2 _ h1 h2 _ _ hm
    (fun g k hk => hs.1 k hk g) g
  rwa [hs.2, one_mul] at this

end Split

section Inert

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [CharZero F]
  (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem indicator_eq_intInd : Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ) = intInd := by
  funext x
  by_cases h : x ∈ 𝒪[E]
  · rw [Set.indicator_of_mem (show x ∈ {x : E | x ∈ 𝒪[E]} from h)]
    simp [intInd, h]
  · rw [Set.indicator_of_notMem (show x ∉ {x : E | x ∈ 𝒪[E]} from h)]
    simp [intInd, h]

theorem Wc_intInd_right (h2 : Module.finrank F E = 2) (χ : AddChar F Circle) (η : Fˣ →* ℂˣ)
    (σ : E ≃ₐ[F] E) (c : Eˣ →* ℂˣ) (hχ : Ad3.IsStd χ) (hc : IsUnramifiedChar c)
    (hη1 : ∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) (hηu : IsUnramifiedChar η)
    (hform : ∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det →
      GL2LocalData.rW χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => intInd (x * (t : E))) 1 =
      (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) *
        intInd ((t : E) * algebraMap F E (mRow g)⁻¹))
    (g k : GL (Fin 2) F) (hk : k ∈ GLnLocal.integralGL F 2) :
    GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd (g * k) =
      GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd g := by
  classical
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  have hrow := RowIwasawa.iwasawa_lower_row F
  have hdk : modulus (k.val).det = 1 := by
    have h1 := (hrow 1 k hk).2.1
    simpa using h1
  obtain ⟨s, hs⟩ : ∃ s : Eˣ, Algebra.norm F (s : E) = (k.val).det := by
    have hk0 : (k.val).det ≠ 0 := (Matrix.GeneralLinearGroup.det k).ne_zero
    have h1 := hη1 (Units.mk0 _ hk0)
    rw [InertAsm.char_congr η hηu (u := Units.mk0 _ hk0) (v := 1) (by simpa using hdk), map_one,
      Units.val_one, Units.val_mk0, GL2LocalData.nsg] at h1
    by_contra hn
    rw [if_neg hn] at h1
    norm_num at h1
  by_cases hg : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · obtain ⟨t, ht⟩ := hg
    have ht' : Algebra.norm F ((t * s : Eˣ) : E) = ((g * k).val).det := by
      rw [Units.val_mul, map_mul, ht, hs, Units.val_mul, Matrix.det_mul]
    rw [InertAsm.Wc_eq hc hform _ _ ht', InertAsm.Wc_eq hc hform _ _ ht]
    obtain ⟨hm0, hdet, hmm, hx⟩ := hrow g k hk
    exact InertAsm.val_eq hχ hη1 hηu hc ht ht' hm0 (hrow (g * k) 1 (one_mem _)).1 hdet hmm hx
  · have hg' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((g * k).val).det := by
      rintro ⟨t', ht'⟩
      refine hg ⟨t' * s⁻¹, ?_⟩
      have hs0 : Algebra.norm F (s : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 s.ne_zero
      have hmul : Algebra.norm F ((t' * s⁻¹ : Eˣ) : E) * Algebra.norm F (s : E) =
          Algebra.norm F (t' : E) := by
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right]
      have hd : ((g * k).val).det = (g.val).det * (k.val).det := by
        rw [Units.val_mul, Matrix.det_mul]
      rw [ht', hs, hd] at hmul
      exact mul_right_cancel₀ (hs ▸ hs0) hmul
    rw [GL2LocalData.Wc, GL2LocalData.Wc, dif_neg hg, dif_neg hg']

theorem Wc_std_eq (h2 : Module.finrank F E = 2) (hcont : Continuous (algebraMap F E))
    (hord : GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1)
    (χ : AddChar F Circle) (hχ : Ad3.IsStd χ) (σ : E ≃ₐ[F] E) (hσ : σ ≠ AlgEquiv.refl)
    (η : Fˣ →* ℂˣ) (hη : ∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) (c : Eˣ →* ℂˣ)
    (hc : IsUnramifiedChar c) (b : ℂˣ)
    (hb : b ^ 2 = c (Units.map (algebraMap F E).toMonoidHom (unifUnit F))) (g : GL (Fin 2) F) :
    GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) (GL2LocalData.lamE E χ η) c
                 (Set.indicator {x : E | x ∈ 𝒪[E]} 1) g =
      Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![b, -b] g := by
  obtain ⟨η', hη'⟩ := GlobalTheory.CompanionTheory.SphTheta.UnramQuad.exists_quadChar_unramified F E h2 hcont hord
  have hηe : η = η' := by
    ext a
    rw [hη, hη'.1]
  subst hηe
  have hstd := GlobalTheory.CompanionTheory.SphTheta.isStd_chE_of_ord_unif F E h2 hcont hord χ hχ
  have hlam := GlobalTheory.CompanionTheory.LamUnr.lamE_eq_one F E χ η hχ hstd hη'.2.1 hη'.2.2.1
  have hform := GlobalTheory.CompanionTheory.SphTheta.inert_rw F E h2 hcont hord χ η σ hσ hχ hstd hη'
    (GlobalTheory.CompanionTheory.NormGauss.gauss_main F E h2 hcont hord χ η hχ hstd hη')
  rw [hlam, indicator_eq_intInd]
  have hψ : ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar χ) x = 1 := by
    intro x hx
    have h1 := isTrivialOn_addCharConductor hχ.1 hχ.2.1 x
      (by rw [hχ.2.2]; exact mem_valBall_zero_iff.2 hx)
    simp [h1]
  have hg := Spherical.eq_iwasawa g
  have hu := Spherical.iwasawaUnip_mem g
  have hk := Spherical.iwasawaInt_mem g
  set u := Spherical.iwasawaUnip g
  set k := Spherical.iwasawaInt g
  set l := Iwasawa.iwasawaExponent F 2 g
  rw [hg, Spherical.sphericalWhittaker_apply hψ _ hu hk,
    Wc_intInd_right F E h2 χ η σ c hχ hc hη'.1 hη'.2.1 hform _ k hk, mul_assoc,
    GlobalTheory.CompanionTheory.SphTheta.WcLeft.Wc_unipotent_mul F E h2 hcont hord χ η σ c hχ hc hη' hform u _ hu,
    GlobalTheory.T.quadratic_extension_uniformizer_valuation F E h2 hcont hord χ η σ c hχ hc hη' hform b hb l]
  have hpsi : Whittaker.psiN (Circle.coeHom.compAddChar χ) u = (χ (u.val 0 1) : ℂ) := by
    simp [Whittaker.psiN, Whittaker.superdiagSum, Fin.sum_univ_two]
    rfl
  rw [hpsi]
  split_ifs with hl
  · ring
  · simp

end Inert

variable {K : Type} [Field K] [NumberField K]

theorem key (hd : Module.finrank ℚ K = 2) (D : Dat) (DK : DatK K) (hbc : IsBC D DK)
    (c : HeckeCharacter K) (v : Pl) (hv : v ∉ D.bad) (hw : Th.Unr c v)
    (Wt : GL (Fin 2) (Qv v) → ℂ) (hth : Th.StdTh c v Wt) :
    ∃ y : Fin 2 → ℂˣ, (∀ j, ‖((y j : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ g, Wt g = Spherical.sphericalWhittaker (Circle.coeHom.compAddChar (GP.psiF v)⁻¹) y g) ∧
      ∀ s : ℂ, lfV DK c v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * ((y j : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ ∧
        lfV DK c⁻¹ v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((y j)⁻¹ : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  have hχ : IsStd (GP.psiF v)⁻¹ := GlobalTheory.CompanionTheory.SphStd.isStd_psiF_inv v
  rcases hth with ⟨w₁, w₂, i₁, i₂, hne, rfl⟩ | ⟨w, i, hu, σ, η, hσ, hη, rfl⟩
  · obtain ⟨u₁, u₂, r₁, r₂, hl⟩ := GlobalTheory.CompanionTheory.SplitPrime.split_lfV K hd D DK hbc c v hv hw w₁ w₂ hne
    refine ⟨_, fun j => ?_, fun g => WcS_std_eq _ hχ _ _ u₁ u₂ r₁ r₂ g, hl⟩
    fin_cases j
    · exact u₁.2 _
    · exact u₂.2 _
  · obtain ⟨hfin, -, hb⟩ := GlobalTheory.CompanionTheory.InertFactor.lfV_inert K hd D DK hbc c v hv hw w hu
    have hord : GroundTheory.LocalField.ord (algebraMap (Qv v) (Kv K w) (unifUnit (Qv v) : Qv v)) = 1 := by
      rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K hd v (fun w' _ => (hw w').2) with
        ⟨w₁, w₂, h₁, h₂, hne⟩ | ⟨w', hw', -, -, ho⟩
      · exact absurd ((hu w₁ h₁).trans (hu w₂ h₂).symm) hne
      · obtain rfl := hu w' hw'
        exact ho
    have hU := isUnit1_localChar c w
    obtain ⟨b, hb2, hbn⟩ := exists_sqrt_unit
      (localChar c w (Units.map (algebraMap (Qv v) (Kv K w)).toMonoidHom (unifUnit (Qv v)))) (hU.2 _)
    refine ⟨![b, -b], fun j => ?_, fun g => Wc_std_eq (Qv v) (Kv K w) hfin
      (continuous_adicCompletionMap v w) hord _ hχ σ hσ η hη _ (hw w).1 b hb2 g, hb b hb2⟩
    fin_cases j
    · exact hbn
    · simpa using hbn

theorem main : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.CasselmanShalikaStandardVector K := by
  intro K _ _ hd D DK hbc c v hv hw Wt hth s hs
  obtain ⟨y, hy, hW, hl⟩ := key hd D DK hbc c v hv hw Wt hth
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  obtain ⟨-, h1, -⟩ := GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ
  have hone : GP.sph D v 1 = 1 := Spherical.sphericalWhittaker_one h1 _
  obtain ⟨a, b⟩ := GlobalTheory.CompanionTheory.UnramifiedZeta.unramified_sum (Qv v) (GP.psiF v) hψ (D.ν v) (D.unit v) (D.unr v hv) y hy Wt hW s hs
  rw [hone, one_mul, one_mul]
  exact ⟨a.trans (hl s).1.symm, b.trans (hl s).2.symm⟩

end GlobalTheory.CompanionTheory.SplitStandardVector
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.SplitSph

theorem sphs_direct : Ad3.K.QuadraticBaseChangeGL3.Th.SPHS := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 hcond c₁ c₂ h₁ h₂
  rw [GlobalTheory.CompanionTheory.SplitStandardVector.indicator_eq_phiS]
  exact GlobalTheory.CompanionTheory.SplitStandardVector.sphN_WcS_phiS χ c₁ c₂ ⟨hχ, hχ1, hcond⟩ h₁ h₂

end GlobalTheory.CompanionTheory.SphTheta.SplitSph
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LamUnr

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_isUnramifiedChar {μ : Fˣ →* ℂˣ} (hu : IsUnramifiedChar μ) : Continuous μ := by
  refine continuous_of_continuousAt_one μ ?_
  have hop : (unitFiltrationUnits F 0 : Set Fˣ) ∈ nhds (1 : Fˣ) :=
    (isOpen_unitFiltrationUnits 0).mem_nhds (Subgroup.one_mem _)
  refine ContinuousAt.congr (f := fun _ => (1 : ℂˣ)) continuousAt_const ?_
  filter_upwards [hop] with x hx
  rw [show μ x = 1 from hu hx]

theorem unit_mem_of_ord_eq_zero {u : Fˣ} (h : ord (u : F) = 0) : (u : F) ∈ 𝒪[F] := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord u.ne_zero, h]

theorem inv_mem_of_ord_eq_zero {u : Fˣ} (h : ord (u : F) = 0) : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
  have h1 : ord (((u⁻¹ : Fˣ)) : F) = 0 := by
    have := ord_mul (K := F) u.ne_zero (u⁻¹).ne_zero
    simp only [Units.mul_inv, ord_one, h, zero_add] at this
    exact this.symm
  exact unit_mem_of_ord_eq_zero h1

end

theorem lamU : Ad3.K.QuadraticBaseChangeGL3.Th.NORMU → Ad3.K.QuadraticBaseChangeGL3.Th.LAMU := by
  intro hN F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη h0 hres
  have hnorm := hN F χ hχ hχ1 E hd hc σ hσ η hη hres
  have hsq : ∀ a, η a * η a = 1 := by
    intro a
    apply Units.ext
    rw [Units.val_mul, hη a, Units.val_one]
    unfold GL2LocalData.nsg
    split_ifs <;> simp
  have hun : IsUnramifiedChar η := by
    rw [isUnramifiedChar_iff]
    intro u hu
    apply Units.ext
    rw [hη u, Units.val_one]
    unfold GL2LocalData.nsg
    exact if_pos (hnorm u (unit_mem_of_ord_eq_zero hu) (inv_mem_of_ord_eq_zero hu))
  have hnm : ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1 := by
    rw [hη]
    unfold GL2LocalData.nsg
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.GlueSign.lamE_eq (continuous_of_isUnramifiedChar hun) hnm hsq,
      localEpsilon_of_isUnramified hun, h0]
    simp
  · unfold GL2LocalData.nsg
    refine if_pos (hnorm (-1) (by simp) ?_)
    simp

end GlobalTheory.CompanionTheory.LamUnr
end
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WSupport

variable {K : Type} [Field K] [NumberField K]

theorem sphN_of_std (hS : Ad3.K.QuadraticBaseChangeGL3.Th.STDSPH K) (h2 : Module.finrank ℚ K = 2) {c : HeckeCharacter K} {v : Pl}
    (m : LM c v) (hok : m.ok) (hU : Unr c v) (hstd : m.std) : SphN m.W := by
  cases m with
  | sp w₁ w₂ Φ =>
    obtain ⟨hne, -, -⟩ := hok
    have hΦ : Φ = _ := hstd
    subst hΦ
    exact (hS h2 c v hU _ (Or.inl ⟨w₁, w₂, inferInstance, inferInstance, hne, rfl⟩)).1
  | ns w σ η Φ =>
    obtain ⟨hu, hσ, hη, -⟩ := hok
    have hΦ : Φ = _ := hstd
    subst hΦ
    exact (hS h2 c v hU _ (Or.inr ⟨w, inferInstance, hu, σ, η, hσ, hη, rfl⟩)).1

theorem W_eq_zero_of_not_plus {c : HeckeCharacter K} {v : Pl} (m : LM c v) (g : GL (Fin 2) (Qv v))
    (h : ¬ m.plus g) : m.W g = 0 := by
  cases m with
  | sp w₁ w₂ Φ => exact absurd trivial h
  | ns w σ η Φ =>
    simp only [LM.W]
    unfold GL2LocalData.Wc
    exact dif_neg h

theorem wsup_of_stdsph (hS : Ad3.K.QuadraticBaseChangeGL3.Th.STDSPH K) : Ad3.K.QuadraticBaseChangeGL3.Th.WSUP K := by
  classical
  intro h2 c n t M hM g hg
  obtain ⟨hok, S0, hS0⟩ := hM
  unfold WM pw2
  by_cases hdet : 0 < ((GL2Classical.realPart g).val).det
  · have hv : ∃ v, ¬ (M v).plus (finAt v g) := by
      by_contra hcon
      push Not at hcon
      exact hg ⟨hcon, hdet⟩
    obtain ⟨v₀, hv₀⟩ := hv
    obtain ⟨S, hSi⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
    have hz : ∏ᶠ v, (M v).W (finAt v g) = 0 := by
      refine finprod_eq_zero _ v₀ (W_eq_zero_of_not_plus _ _ hv₀) ?_
      refine (S0 ∪ S).finite_toSet.subset ?_
      intro v hv
      by_contra hn
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
      obtain ⟨h1, h3⟩ := hn
      apply hv
      have hsph := sphN_of_std hS h2 (M v) (hok v) (hS0 v h1).1 (hS0 v h1).2
      show (M v).W (finAt v g) = 1
      have hk := hsph.1 _ (hSi v h3) 1
      rw [one_mul] at hk
      rw [hk]
      exact hsph.2
    rw [hz, mul_zero]
  · have : WcR (chC n (Complex.I * t)) (PhiInf n) (GL2Classical.realPart g) = 0 := by
      unfold WcR
      exact dif_neg hdet
    rw [this, zero_mul]

theorem wsup : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.Th.WSUP K := by
  intro K _ _
  have hN := GlobalTheory.CompanionTheory.UnitNormUnr.normU
  have hF : Ad3.K.QuadraticBaseChangeGL3.Th.SPHF := GlobalTheory.CompanionTheory.SphFUnr.sphf GlobalTheory.T.weil_induced_representation_hypothesis
    (GlobalTheory.CompanionTheory.PiKFUnr.pikf GlobalTheory.CompanionTheory.RwKF.rwkf GlobalTheory.CompanionTheory.NormModulus.wMod hN) hN
  exact wsup_of_stdsph (GlobalTheory.CompanionTheory.StdSphOf.stdsph K hF GlobalTheory.CompanionTheory.SphTheta.SplitSph.sphs_direct
    (GlobalTheory.CompanionTheory.LamUnr.lamU hN) hN)

end GlobalTheory.CompanionTheory.WSupport
end
end
