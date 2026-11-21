import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RefCharValues



theorem exists_principal (L : Type) [Field L] [NumberField L] (a : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (h1 : ClassGroup.mk L ((GlobalTheory.Mem.UnitIndex.idealHom L).toHomUnits a) = 1) : ∃ e : Lˣ, ∀ v, Valued.v
      ((a * (FiniteAdeleRing.unitEmbedding (𝓞 L) L e)⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ).1 v) = 1 := by
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf a = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  refine ⟨Units.mk0 x hx0, (GlobalTheory.Idele.smul_eq_self_iff (R := 𝓞 L) (K := L) _ (I := 1) one_ne_zero).1 ?_⟩
  rw [GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, GlobalTheory.Idele.idealOf_unitEmbedding, hx']
  exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)

theorem exists_class (D : D7) : ∃ cl : (AE D)ˣ →* ClassGroup (𝓞 D.host.E), ∀ x, cl x = 1 → ∃ e : D.host.Eˣ,
    finPart D ((x * (Units.map (incA D).toMonoidHom e)⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧
    finPart D (((x * (Units.map (incA D).toMonoidHom e)⁻¹)⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  let φ : (AE D)ˣ →* (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom
  refine ⟨(ClassGroup.mk D.host.E).comp ((GlobalTheory.Mem.UnitIndex.idealHom D.host.E).toHomUnits.comp φ), fun x hx => ?_⟩
  obtain ⟨e, he⟩ := exists_principal D.host.E (φ x) hx
  have hφ : φ (Units.map (incA D).toMonoidHom e) = FiniteAdeleRing.unitEmbedding (𝓞 D.host.E) D.host.E e :=
    Units.ext (h1 e)
  rw [← hφ, ← map_inv, ← map_mul] at he
  refine ⟨e, ?_⟩
  generalize x * (Units.map (incA D).toMonoidHom e)⁻¹ = u at he
  refine ⟨(h2 _).2 fun P => (he P).le, (h2 _).2 fun P => ?_⟩
  have h3 : (φ u).1 P * (φ u⁻¹).1 P = 1 := by
    have : (φ u).1 * (φ u⁻¹).1 = 1 := by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) this
  have h4 := congrArg Valued.v h3
  rw [map_mul, he P, one_mul, map_one] at h4
  exact h4.le

theorem sign_zpow_even (z : ℂ) (h : z ≠ 0) (k : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * k) = (z / starRingEnd ℂ z) ^ k := by
  rw [zpow_mul]
  congr 1
  have h1 : (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using h
  rw [zpow_ofNat, div_pow, h1]
  field_simp



end GlobalTheory.RefCharValues
