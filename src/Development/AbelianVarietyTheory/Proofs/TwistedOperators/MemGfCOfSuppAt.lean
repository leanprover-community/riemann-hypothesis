import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Formalism.LocalToGlobal.UnitaryNorms.CharExGen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUniformiserValueIsAlgebraic
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupFixesVacuumDefiniteBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumFinitePairVacuumAlgebraicCombination
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointsMemOfLevelAndSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

section Reformulated
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open IsDedekindDomain NumberField Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinValAlg

theorem isAlgebraic_unit_zpow {z : ℂ} (hz : IsAlgebraic ℚ z) (n : ℤ) :
    IsAlgebraic ℚ ((z / ((‖z‖ : ℝ) : ℂ)) ^ n) := by
  have hc : IsAlgebraic ℚ (starRingEnd ℂ z) := hz.algHom (starRingEnd ℂ).toRatAlgHom
  have hn : IsAlgebraic ℚ (((‖z‖ : ℝ) : ℂ)) := by
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [← Complex.conj_mul']
    exact (mem_algebraicClosure_iff.1 (mul_mem (mem_algebraicClosure_iff.2 hc) (mem_algebraicClosure_iff.2 hz)))
  rw [← mem_algebraicClosure_iff] at hz hn ⊢
  exact zpow_mem (div_mem hz hn) n

variable {D : D7}

theorem finPart_incA (e : D.host.E) : finPart D (incA D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e := by
  change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem int_of_val_eq_one (ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) (z : (AE D)ˣ)
    (hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (z : AE D)) P) = 1) :
    finPart D (z : AE D) ∈ intAE D ∧ finPart D ((z⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  refine ⟨(hι2 _).2 fun P => (hv P).le, (hι2 _).2 fun P => le_of_eq ?_⟩
  have e : ι (finPart D ((z⁻¹ : (AE D)ˣ) : AE D)) * ι (finPart D (z : AE D)) = 1 := by
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  have e2 : ι (finPart D ((z⁻¹ : (AE D)ˣ) : AE D)) P * ι (finPart D (z : AE D)) P = 1 := by
    have := congrArg (fun w : FiniteAdeleRing (𝓞 D.host.E) D.host.E => w P) e
    exact this
  have := congrArg Valued.v e2
  rwa [map_mul, hv, mul_one, map_one] at this

theorem ι_finPart_pow_mul (ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (x : (AE D)ˣ) (h : ℕ) (k : D.host.Eˣ) :
    ι (finPart D ((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D)) =
      ι (finPart D (x : AE D)) ^ h * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) := by
  have e : ((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D) = (x : AE D) ^ h * incA D (k : D.host.E) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  rw [e, map_mul, map_pow, map_mul, map_pow, finPart_incA, hι1]

theorem exists_pow_mul_int (x : (AE D)ˣ) : ∃ h : ℕ, 0 < h ∧ ∃ k : D.host.Eˣ,
    finPart D (((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ)) : AE D) ∈ intAE D ∧
    finPart D ((((x ^ h * Units.map (incA D).toMonoidHom k)⁻¹ : (AE D)ˣ)) : AE D) ∈ intAE D := by
  obtain ⟨ι, hι1, hι2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h, hh, hX⟩ := Formalism.L2.Host.CharEx.classExp D.host.E
  obtain ⟨a, a', haa, haa', ha⟩ : ∃ a a' : Af D.host.F ⊗[D.host.F] D.host.E, a * a' = 1 ∧ a' * a = 1 ∧
      a = finPart D (x : AE D) :=
    ⟨_, _, by rw [← map_mul, Units.mul_inv, map_one], by rw [← map_mul, Units.inv_mul, map_one], rfl⟩
  let X : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨((1 : InfiniteAdeleRing D.host.E), ι a), ((1 : InfiniteAdeleRing D.host.E), ι a'),
      Prod.ext (show (1 : InfiniteAdeleRing D.host.E) * 1 = 1 from mul_one _)
        (show ι a * ι a' = 1 by rw [← map_mul, haa, map_one]),
      Prod.ext (show (1 : InfiniteAdeleRing D.host.E) * 1 = 1 from mul_one _)
        (show ι a' * ι a = 1 by rw [← map_mul, haa', map_one])⟩
  obtain ⟨k, hk⟩ := hX X
  refine ⟨h, hh, k, int_of_val_eq_one ι hι2 _ fun P => ?_⟩
  rw [ι_finPart_pow_mul ι hι1, ← ha]
  have e : ((X ^ h * Neutral.B1.diagUnits D.host.E k : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      AdeleRing (𝓞 D.host.E) D.host.E).2 = ι a ^ h * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  rw [← e]
  exact hk P

end GlobalTheory.FinValAlg

namespace GlobalTheory.FinValAlg

variable {D : D7}

theorem infPart_incA (e : D.host.E) : infPart D (incA D e) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] e := by
  change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem infPart_pairE (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    infPart D (Formalism.L2.Fam.ThC.pairE a b) = a := Formalism.L2.Fam.ThC.fst_pairE a b

theorem finPart_pairE (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (Formalism.L2.Fam.ThC.pairE a b) = b := Formalism.L2.Fam.ThC.snd_pairE a b

theorem pairE_mul_eq_one (z : (AE D)ˣ) :
    Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 * Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 = 1 := by
  refine Formalism.L2.Fam.ThC.ae_ext ?_ ?_
  · rw [map_mul, infPart_pairE, infPart_pairE, ← map_mul, Units.mul_inv]
  · rw [map_mul, finPart_pairE, finPart_pairE, mul_one, map_one]

theorem pairE_mul_eq_one' (z : (AE D)ˣ) :
    Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 * Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 = 1 := by
  refine Formalism.L2.Fam.ThC.ae_ext ?_ ?_
  · rw [map_mul, infPart_pairE, infPart_pairE, ← map_mul, Units.inv_mul]
  · rw [map_mul, finPart_pairE, finPart_pairE, mul_one, map_one]

set_option maxHeartbeats 1000000 in

theorem exists_decomp (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) :
    ∃ h : ℕ, 0 < h ∧ ∃ (k : D.host.Eˣ) (y u : (AE D)ˣ), finPart D (y : AE D) = 1 ∧ Formalism.L2.Pj.FinUnit u ∧
      infPart D (y : AE D) = infPart D (incA D (k : D.host.E)) ∧ x ^ h * Units.map (incA D).toMonoidHom k = y * u := by
  obtain ⟨h, hh, k, h1, h2⟩ := exists_pow_mul_int x
  refine ⟨h, hh, k, ?_⟩
  generalize hz : x ^ h * Units.map (incA D).toMonoidHom k = z at h1 h2
  have hiz : infPart D (z : AE D) = infPart D (incA D (k : D.host.E)) := by
    rw [← hz, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hx, one_pow, one_mul]
    rfl
  have m1 := pairE_mul_eq_one z
  have m2 := pairE_mul_eq_one' z
  obtain ⟨y, hyv, hyi⟩ : ∃ y : (AE D)ˣ, (y : AE D) = Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 ∧
      ((y⁻¹ : (AE D)ˣ) : AE D) = Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 :=
    ⟨⟨_, _, m1, m2⟩, rfl, rfl⟩
  refine ⟨y, y⁻¹ * z, by rw [hyv, finPart_pairE], ⟨?_, ?_, ?_⟩, by rw [hyv, infPart_pairE, hiz], by rw [mul_inv_cancel_left]⟩
  · rw [Units.val_mul, map_mul, hyi, infPart_pairE, ← map_mul, Units.inv_mul, map_one]
  · rw [Units.val_mul, map_mul, hyi, finPart_pairE, one_mul]; exact h1
  · rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul, hyv, finPart_pairE, mul_one]; exact h2

theorem char_eq_prod {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle} (nτ : D.what₂.Tau → ℤ)
    (hn : ∀ τ (x : (AE D)ˣ), finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ nτ τ)
    (y : (AE D)ˣ) (hy : finPart D (y : AE D) = 1) :
    ((χ y : Circle) : ℂ) = ∏ τ, (θ τ (infPart D (y : AE D)) / (‖θ τ (infPart D (y : AE D))‖ : ℂ)) ^ nτ τ := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom hσ
  let wU : D.what₂.Tau → ℂˣ := fun τ => (y.isUnit.map ((θ τ).comp (infPart D))).unit
  have hwU : ∀ τ, ((wU τ : ℂˣ) : ℂ) = θ τ (infPart D (y : AE D)) := fun τ => rfl
  let f : (D.what₂.Tau → ℂ)ˣ →* (AE D)ˣ := Units.map e
  have hf1 : ∀ W, finPart D ((f W : (AE D)ˣ) : AE D) = 1 := fun W => e1 _
  have hf2 : ∀ W τ, θ τ (infPart D ((f W : (AE D)ˣ) : AE D)) = (W : D.what₂.Tau → ℂ) τ := fun W τ => e2 _ τ
  have hy' : y = ∏ τ, f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ))) := by
    rw [← map_prod, ← map_prod, Finset.univ_prod_mulSingle]
    apply Units.ext
    refine GlobalTheory.SplitCharExp.ext_of_chart hσ (by rw [hy, hf1]) fun τ => ?_
    rw [hf2]
    exact (hwU τ).symm
  have hc : ((χ y : Circle) : ℂ) = ∏ τ, ((χ (f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ)))) : Circle) : ℂ) := by
    show Circle.coeHom (χ y) = ∏ τ, Circle.coeHom (χ (f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ)))))
    rw [← map_prod, ← map_prod, ← hy']
  rw [hc]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hs : ∀ τ', θ τ' (infPart D ((f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ))) : (AE D)ˣ) : AE D)) =
      (((Pi.mulSingle τ (wU τ) : D.what₂.Tau → ℂˣ) τ' : ℂˣ) : ℂ) := fun τ' => by rw [hf2]; rfl
  rw [hn τ _ (hf1 _) fun τ' h => by rw [hs, Pi.mulSingle_eq_of_ne h, Units.val_one], hs, Pi.mulSingle_eq_same, hwU]

theorem isAlgebraic_of_infPart_eq_one : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ},
    IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) := by
  intro D θ χ n hθ hχ hr x hx
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ n τ hθ hχ hr
  choose nτ hn2 hn using ha
  have hn' : ∀ τ (x : (AE D)ˣ), finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ nτ τ :=
    fun τ => (hn τ).2 θ hθ
  obtain ⟨h, hh, k, y, u, hy1, hu, hyi, e⟩ := exists_decomp x hx
  obtain ⟨-, -, -, m, hm, hum⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ.1
  have hyalg : IsAlgebraic ℚ ((χ y : Circle) : ℂ) := by
    rw [char_eq_prod hθ nτ hn' y hy1, ← mem_algebraicClosure_iff]
    refine prod_mem fun τ _ => ?_
    rw [mem_algebraicClosure_iff, hyi, infPart_incA, (hθ τ).1]
    exact isAlgebraic_unit_zpow (GlobalTheory.isAlgebraic_embedding_apply _ _) _
  have e2 : χ x ^ (h * m) = χ y ^ m := by
    have := congrArg (fun g => χ g ^ m) e
    simp only [map_mul, mul_pow, hum u hu, mul_one, hχ.2 k, one_pow, map_pow] at this
    rw [pow_mul]
    exact this
  refine IsAlgebraic.of_pow (Nat.mul_pos hh hm) ?_
  rw [← Circle.coe_pow, e2, Circle.coe_pow, ← mem_algebraicClosure_iff]
  exact pow_mem (mem_algebraicClosure_iff.2 hyalg) _

end GlobalTheory.FinValAlg

end

end Reformulated

theorem GlobalTheory.FinValAlg.finite_values_isAlgebraic : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ}, IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) :=
  GlobalTheory.FinValAlg.isAlgebraic_of_infPart_eq_one
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ}, IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) := by
  atlas_forward_decl GlobalTheory.FinValAlg.finite_values_isAlgebraic
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixPair

theorem om_pow_eq {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ))
    (g : GA D S × GA D V) (f : WO S V → ℂ) (c : ℂ) (hc : om g f = c • f) : ∀ m : ℕ, om (g ^ m) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    rw [pow_succ, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

set_option maxHeartbeats 1000000 in

theorem pair_fix_vacO : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S N k → GlobalTheory.Member.FinCong T N k' → om (k, k') v = v := by
  intro D ψ θ S T sS sT ΛS ΛT v χS χT om hvac hsdS hsdT hcS hcT hW
  have hθ : IsInfFam θ := hvac.2.inf
  have hev := (GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).1
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC S, ∀ x' ∈ GfC T, GlobalTheory.Member.FinCong S n.factorial x →
      GlobalTheory.Member.FinCong T n.factorial x' →
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T x x' u ∈
          (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' u hu hu' using hne
    have ht : Filter.Tendsto (fun n => ((k n, k' n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc).prodMk_nhds
        (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk' hkc')
    obtain ⟨n, hn⟩ := (ht.eventually hev).exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S n₁.factorial k →
      GlobalTheory.Member.FinCong T n₁.factorial k' → ∃ c : ℂ, ‖c‖ = 1 ∧ om (k, k') v = c • v := by
    intro k hk k' hk' hc hc'
    have hΛ : ∀ u : WO S T, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
        (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T
        (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        u = actO S T k k' u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO S T k⁻¹ k'⁻¹ u, hn₁ k⁻¹ (inv_mem hk) k'⁻¹ (inv_mem hk')
          (GlobalTheory.Member.PrincLevel.finCong_inv hc) (GlobalTheory.Member.PrincLevel.finCong_inv hc') u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ k'⁻¹ u
        rw [inv_inv, inv_inv] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk k' hk' hc hc' u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ
      sS sS sT sT _ _ _ _ k k'
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hk τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hk' τ, Matrix.one_mul, Matrix.mul_one]) hΛ v hvac
    exact GlobalTheory.VacUnique.vacUniqueO D ψ θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T)
      sS sT (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT ΛS ΛT
      hsdS hsdT v _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun p : GA D S × GA D T => om p v w₀ := hW.om_cont _ hvac.2.theta w₀
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S (n₁.factorial * n.factorial) k →
      GlobalTheory.Member.FinCong T (n₁.factorial * n.factorial) k' → om (k, k') v = v := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om (k n ^ m, k' n ^ m) v = c • v ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (k' n) (hk' n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
        (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc' n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (by rw [← Prod.pow_mk]; exact om_pow_eq om _ v c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have hmem' : ∀ n, k' n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k' n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) from ⟨hk' n, hkc' n⟩) _
    have ht : Filter.Tendsto (fun n => ((k n ^ m n, k' n ^ m n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)).prodMk_nhds
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k' n ^ m n) (fun n => (hmem' n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem' n).2))
    have e1 : om (1 : GA D S × GA D T) v w₀ = v w₀ := by
      rw [map_one]
      rfl
    have h2 : Filter.Tendsto (fun n => om (k n ^ m n, k' n ^ m n) v w₀) Filter.atTop (𝓝 (v w₀)) := by
      have := (hcont.tendsto 1).comp ht
      rw [← e1]
      exact this
    have hpos : 0 < ‖v w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (v w₀)]
  obtain ⟨n, hn⟩ := key
  exact ⟨n₁.factorial * n.factorial, Nat.mul_pos n₁.factorial_pos n.factorial_pos,
    fun k hk k' hk' hc hc' => hn k hk k' hk' hc hc'⟩

end GlobalTheory.VacFixPair
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruent_pairs_fix_vacuum_weilDatum : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S N k → GlobalTheory.Member.FinCong T N k' → om (k, k') v = v := by
  atlas_forward_decl GlobalTheory.VacFixPair.pair_fix_vacO
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitAlgForm

open GlobalTheory.SplitScalar GlobalTheory.LevelSeries.IdemSumForm GlobalTheory.AlgWave

theorem psi_ne_zero {G : Type} [AddGroup G] (ψ : AddChar G ℂ) (x : G) : ψ x ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem fin_smul {D : D7} {m n : ℕ} (a : AE D) {x : Mx D m n} (hx : x.map (infPart D) = 0) :
    (a • x).map (infPart D) = 0 := by
  ext i j
  have : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show infPart D (a * x i j) = 0
  rw [RingHom.map_mul, this, mul_zero]

theorem fin_add {D : D7} {m n : ℕ} {x y : Mx D m n} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  rw [Matrix.map_add _ (map_add (infPart D)), hx, hy, add_zero]

set_option maxHeartbeats 1000000 in

theorem exists_alg_form : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e → ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) →
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      ℓ v = 1 ∧ ∀ p, IsAlgebraic ℚ (ℓ (heisO ψ S T (w p) v)) := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT e he n w hw
  classical
  have hψ : IsStdChar D ψ (-1) := hv.1
  obtain ⟨hd, -, hsg⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  set Λ : AddSubgroup (WO S T) := latO S T (ΛS : Set (Fin S.rank → D.host.E))
    (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛdef
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ := fun a ha =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
  have hΛfin : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => latO_fin hu
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hvth : IsThetaFunO ψ S T v := hv.2.theta
  have hlat : IsLatVac (heisO ψ S T) Λ v := hv.2.lat
  have hsign : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u v = ε • v := fun u hu => by
    obtain ⟨ε, hε, h⟩ := hsg v hlat u hu
    exact ⟨ε, hε, h v hlat⟩
  have hεQ : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ε ∈ Qb ∧ ε ≠ 0 := by
    rintro ε (rfl | rfl)
    · exact ⟨one_mem _, one_ne_zero⟩
    · exact ⟨neg_mem (one_mem _), neg_ne_zero.2 one_ne_zero⟩
  have hpsi : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplO S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psi_mem hψ hS hT hx hy
  have hpsiH : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplOH S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psiH_mem hψ hS hT hx hy

  have hcS : IsSplitIdem D (cA D e) := isSplitIdem_conj he
  have he1 : e * e = e := he.1
  have hec : e * (cA D e) = 0 := he.2.1
  have hce : (cA D e) * e = 0 := by rw [mul_comm]; exact hec
  have hc1 : (cA D e) * (cA D e) = (cA D e) := by rw [← RingHom.map_mul, he1]
  have hcc : cA D (cA D e) = e := GlobalTheory.DualPairCheck.cA_cA e
  have hq1 : (1 - (e + (cA D e))) * (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by linear_combination he1 + hc1 + 2 * hec
  have hcq : cA D (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by
    rw [map_sub, map_one, map_add, hcc, add_comm (cA D e) e]
  have hcq0 : (cA D e) * (1 - (e + (cA D e))) = 0 := by linear_combination -hc1 - hce
  have hqc0 : cA D (1 - (e + (cA D e))) * (cA D e) = 0 := by rw [hcq, mul_comm]; exact hcq0
  have hdec : ∀ x : WO S T, (cA D e) • x + (e • x + (1 - (e + (cA D e))) • x) = x := fun x => by
    rw [← add_smul, ← add_smul, ← add_assoc, add_comm (cA D e) e, add_sub_cancel, one_smul]

  have caseB : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → (1 - (e + (cA D e))) • x ∈ Λ → ℓ (heisO ψ S T x v) ∈ Qb := by
    intro ℓ hinv h1 x hx hx'
    obtain ⟨ε, hε, hεv⟩ := hsign _ hx'
    have hxe : IsHalf e (e • x) := (isHalf_iff _ _).2 (by rw [smul_smul, he1])
    have hxc : IsHalf (cA D e) ((cA D e) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hc1])
    have hxq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    have horth : symplO S T (e • x) ((1 - (e + (cA D e))) • x) = 0 := symplO_eq_zero S T hcq0 hxe hxq
    have e1 : heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v = ε • heisO ψ S T (e • x) v := by
      rw [heisO_add_of_orth ψ S T horth, hεv, heisO_smul]
    have e2 : heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v) =
        ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) • heisO ψ S T x v := by
      rw [heisO_heisO, hdec x]
    have e3 : ℓ (heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v)) =
        ε * ℓ (heisO ψ S T (e • x) v) := by
      rw [hinv _ hxc _ (hth _ _ hvth), e1, map_smul, smul_eq_mul]
    rw [e2, map_smul, smul_eq_mul] at e3
    have hx0 := psi_ne_zero ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x))
    have hpq : ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) ∈ Qb :=
      hpsiH _ _ (fin_smul _ hx) (fin_add (fin_smul _ hx) (fin_smul _ hx))
    have e4 : ℓ (heisO ψ S T x v) = (ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)))⁻¹ *
        (ε * ℓ (heisO ψ S T (e • x) v)) := by
      rw [← e3, inv_mul_cancel_left₀ hx0]
    rw [e4]
    refine mul_mem (inv_mem hpq) (mul_mem (hεQ ε hε).1 ?_)
    by_cases hxΛ : e • x ∈ Λ
    · rw [hlat.2 e he _ hxΛ hxe, h1]; exact one_mem _
    · obtain ⟨l, hl, hlc, hne⟩ := dual_half he1 (fun u hu => half_fin he hu) hd (fun u hu => hΛ (cA D e) hc1 u hu) hxe hxΛ
      have h0 : ℓ (heisO ψ S T (e • x) v) = 0 := by
        have k1 := hinv l hlc _ (hth (e • x) v hvth)
        rw [heisO_comm, hlat.2 (cA D e) hcS l hl hlc, map_smul, smul_eq_mul] at k1
        have : (ψ (symplO S T l (e • x)) - 1) * ℓ (heisO ψ S T (e • x) v) = 0 := by
          rw [sub_mul, k1, one_mul, sub_self]
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
      rw [h0]; exact zero_mem _

  have step : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → ∃ ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ' (heisO ψ S T u f) = ℓ' f) ∧ ℓ' v = 1 ∧
        ℓ' (heisO ψ S T x v) ∈ Qb ∧ ∀ y : WO S T, y.map (infPart D) = 0 →
          ∃ a ∈ Qb, ℓ' (heisO ψ S T y v) = a * ℓ (heisO ψ S T y v) := by
    intro ℓ hinv h1 x hx
    by_cases hB : (1 - (e + (cA D e))) • x ∈ Λ
    · exact ⟨ℓ, hinv, h1, caseB ℓ hinv h1 x hx hB, fun y _ => ⟨1, one_mem _, (one_mul _).symm⟩⟩
    have hex : ¬ ∀ u ∈ Λ, ψ (symplO S T ((1 - (e + (cA D e))) • x) u) = 1 := fun h => hB ((hd _ (fin_smul _ hx)).2 h)
    push_neg at hex
    obtain ⟨u', hu', hne'⟩ := hex
    have huΛ : (1 - (e + (cA D e))) • u' ∈ Λ := hΛ _ hq1 u' hu'
    have huq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • u') := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    rw [symplO_smul, hcq] at hne'
    have hne := psi_skew_ne hne'
    obtain ⟨ε, hε, hεv⟩ := hsign _ huΛ
    obtain ⟨hεQ', hε0⟩ := hεQ ε hε
    have hzQ : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ∈ Qb := hpsi _ _ (hΛfin _ huΛ) hx
    have hk : ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ≠ 0 := by
      rw [← mul_one_sub]
      exact mul_ne_zero hε0 (sub_ne_zero.2 (Ne.symm hne))
    have hcomm : ∀ w₁ : WO S T, heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T w₁ v) =
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') w₁) * ε) • heisO ψ S T w₁ v := fun w₁ => by
      rw [heisO_comm, hεv, heisO_smul, smul_smul]
    refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ •
      (ℓ ∘ₗ (heisL ψ S T ((1 - (e + (cA D e))) • u') - (ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)) • LinearMap.id)),
      fun y hy f hf => ?_, ?_, ?_, fun y hy => ?_⟩
    all_goals simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sub_apply, heisL_apply,
      LinearMap.id_apply, map_sub, map_smul, smul_eq_mul]
    · have hc' : heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T y f) =
          heisO ψ S T y (heisO ψ S T ((1 - (e + (cA D e))) • u') f) := by
        rw [heisO_comm, symplO_eq_zero S T hqc0 huq hy, AddChar.map_zero_eq_one, one_smul]
      rw [hc', hinv y hy _ (hth _ _ hf), hinv y hy f hf]
    · rw [hεv, map_smul, smul_eq_mul, h1, mul_one, mul_one, inv_mul_cancel₀ hk]
    · rw [hcomm, map_smul, smul_eq_mul]
      have : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ε * ℓ (heisO ψ S T x v) -
          ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ℓ (heisO ψ S T x v) = 0 := by ring
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ *
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') y) * ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)),
        mul_mem (inv_mem (sub_mem hεQ' (mul_mem hεQ' hzQ)))
          (sub_mem (mul_mem (hpsi _ _ (hΛfin _ huΛ) hy) hεQ') (mul_mem hεQ' hzQ)), ?_⟩
      rw [hcomm, map_smul, smul_eq_mul]
      ring

  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hv.2.norm.1
    have := hv.2.norm.2 p hp
    simp [nrm2] at this
  obtain ⟨ℓ₀, hℓ₀, hinv₀⟩ := invariant_form (e := (cA D e)) (Λ := Λ) hc1 (by rw [hcc]; exact hec)
    (fun u hu => half_fin hcS hu) hd (fun u hu => by rw [hcc]; exact hΛ e he1 u hu) hv0
    (fun l hl hh => hlat.2 (cA D e) hcS l hl hh) (fun l hl hh => hlat.2 e he l hl (by rwa [hcc] at hh))
  have main : ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ℓ v = 1 ∧
      ∀ p, ℓ (heisO ψ S T (w p) v) ∈ Qb := by
    intro n
    induction n with
    | zero =>
      intro w _
      refine ⟨(ℓ₀ v)⁻¹ • ℓ₀, fun u hu f hf => ?_, ?_, fun p => p.elim0⟩
      · rw [LinearMap.smul_apply, LinearMap.smul_apply, hinv₀ u hu f hf]
      · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hℓ₀]
    | succ n ih =>
      intro w hw
      obtain ⟨ℓ, hinv, h1, halg⟩ := ih (fun p => w p.castSucc) fun p => hw _
      obtain ⟨ℓ', hinv', h1', hlast, hfac⟩ := step ℓ hinv h1 (w (Fin.last n)) (hw _)
      refine ⟨ℓ', hinv', h1', fun p => ?_⟩
      induction p using Fin.lastCases with
      | last => exact hlast
      | cast q =>
        obtain ⟨a, ha, h⟩ := hfac _ (hw q.castSucc)
        rw [h]
        exact mul_mem ha (halg q)
  obtain ⟨ℓ, hinv, h1, halg⟩ := main n w hw
  exact ⟨ℓ, fun u hu f hf => hinv u hu f hf, h1, fun p => mem_algebraicClosure_iff.1 (halg p)⟩

end GlobalTheory.SplitAlgForm

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicInvariantForm_vacuum_splitPlace : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e → ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) →
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      ℓ v = 1 ∧ ∀ p, IsAlgebraic ℚ (ℓ (heisO ψ S T (w p) v)) := by
  atlas_forward_decl GlobalTheory.SplitAlgForm.exists_alg_form
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotFourierSnd

open GlobalTheory.PlaceModel GlobalTheory.AlgWave GlobalTheory.BotFourier GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

theorem unitChar_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hN : IsIntM N) : unitChar ν e N ∈ Qb := by
  obtain ⟨-, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  unfold unitChar
  split_ifs with hu
  · obtain ⟨h1, h2, h3⟩ := hu.choose_spec
    have hdet : N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      let B : Matrix (Fin k) (Fin k) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun a b => ⟨_, hN a b⟩
      have hB : N = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix B := rfl
      rw [hB, ← RingHom.map_det]
      exact (B.det).2
    have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
    have hfu : Formalism.L2.Pj.FinUnit hu.choose := ⟨h1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by
      rw [h2]; exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hdet)), GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h3⟩
    have hpow := hord _ hfu
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := m) hm ?_)
    have e1 : (((ν hu.choose)⁻¹ : Circle) : ℂ) ^ m = Circle.coeHom (((ν hu.choose) ^ m)⁻¹) := by
      rw [← inv_pow, map_pow]; rfl
    rw [e1, hpow, inv_one, map_one]
    exact isAlgebraic_one
  · exact zero_mem _

theorem stdSnd_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D) (βA : GL (Fin A'.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (x : WO A' WW) : stdSnd ν e I a A' WW βA βW x ∈ Qb := by
  unfold stdSnd
  split_ifs with hc
  · exact unitChar_mem hν he (GlobalTheory.CompanionTheory.StdSndTheta.isIntM_rightBlock hc.2.1)
  · exact zero_mem _

set_option maxHeartbeats 2000000 in

theorem isAlgComb_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S WW : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)}
    (hSd : IsSelfDualC S ΛS) (hWd : IsSelfDualC WW ΛT) {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    {vac Φ f : WO S WW → ℂ} (hSB : IsSBHalf e (latO S WW ΛS ΛT fun _ => True) Φ) (hΦ : ∀ x, Φ x ∈ Qb)
    (hth : IsThetaAt ψ (symplO S WW) (heisO ψ S WW) e (latO S WW ΛS ΛT fun _ => True) 1 vac Φ f) :
    GlobalTheory.MovedAlg.IsAlgComb ψ S WW vac f := by
  classical
  have hinf' := GlobalTheory.PlaceDatum.infPart_cA hinf
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  rw [hall Tm hTm]
  set Λ : AddSubgroup (WO S WW) := latO S WW ΛS ΛT fun _ => True with hΛ

  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S WW ΛS ΛT hψ hSd hWd).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S WW _ _ hSd.1.fg hWd.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ ⊓ half S WW a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S WW _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have finX : ∀ x ∈ half S WW e, x.map (infPart D) = 0 := fun x hx =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf ((isHalf_iff S WW).2 hx)
  have finY : ∀ y ∈ half S WW (cA D e), y.map (infPart D) = 0 := fun y hy =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf' ((isHalf_iff S WW).2 hy)
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S WW => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S WW hk a, ← inv_smul_nsmul S WW hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S WW ψ

  obtain ⟨h1, k, hk, h2, h3⟩ := hSB
  have hmem := mem_algSpan (χ := fun x y : WO S WW => ψ (symplO S WW x y)) (X := half S WW e)
    (Y := half S WW (cA D e)) (L := Λ ⊓ half S WW e) (L' := Λ ⊓ half S WW (cA D e)) hb
    (fun x hx y hy => psi_mem hψ hSd hWd (finX x hx) (finY y hy)) inf_le_right inf_le_right
    (fun u hu y hy => (hdual u (finX u hu.2)).1 hu.1 y hy.1)
    (fun x hx h => ⟨(hdual x (finX x hx)).2 fun u hu => by
      have := h _ (hsm _ he' u hu)
      rwa [← symplO_smul, (mem_half S WW).1 hx] at this, hx⟩)
    (half_div S WW e) (half_div S WW _) tf
    (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e hee u hu, ?_⟩
      have := (mem_half S WW).1 ht.2
      rw [← this, htr, smul_add, smul_comm e k u])
    _ hΦ (fun t ht => (isHalf_iff S WW).1 (h1 t ht)) k hk
    (fun u hu => h2 u hu.1 ((isHalf_iff S WW).2 hu.2))
    (fun t ht => ⟨h3 t ht, (half S WW e).nsmul_mem ((isHalf_iff S WW).1 (h1 t ht)) _⟩)

  set V : Submodule Qb (WO S WW → ℂ) := Submodule.span Qb
    {F | ∃ w : WO S WW, w.map (infPart D) = 0 ∧ F = heisO ψ S WW w vac} with hV
  have hvac : Tm (halfInd e Λ) = vac := by simpa using hTm.vac
  have s0 := GlobalTheory.isSBHalf_halfInd e Λ
  have hT : ∀ Ψ ∈ algSpan (fun x y : WO S WW => ψ (symplO S WW x y)) (half S WW e) (half S WW (cA D e))
      (Λ ⊓ half S WW e), Tm Ψ ∈ V := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem _ hh =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hh
      have s1 : IsSBHalf e Λ fun t => ψ (symplO S WW t y) * halfInd e Λ t := by
        obtain ⟨k, hk, hk'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' (S := S) (T := WW) hSd.1 hWd.1 y (finY y hy)
        obtain ⟨a1, k', hk1, a2, a3⟩ := s0
        refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
          fun t ht => ?_⟩
        · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
            rw [mul_nsmul]
            exact a2 _ (nsmul_mem hu k) ((isHalf_iff S WW).2 (nsmul_mem ((isHalf_iff S WW).1 hh) k)) t
          have e2 : ψ (symplO S WW ((k * k') • u) y) = 1 := by
            rw [mul_nsmul']
            refine (hb.nsmul k _ y).trans ((hdual _ (finX _ (nsmul_mem ((isHalf_iff S WW).1 hh) k'))).1
              (nsmul_mem hu k') _ hk')
          simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
        · rw [mul_nsmul']
          exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
      have e1 : wave (fun x y : WO S WW => ψ (symplO S WW x y)) (Λ ⊓ half S WW e) x y =
          fun t => (fun t => ψ (symplO S WW t y) * halfInd e Λ t) (t + x) := by
        rw [halfInd_eq_ind]; rfl
      rw [e1, hTm.trans _ s1 x ((isHalf_iff S WW).2 hx), hTm.modul _ s0 y ((isHalf_iff S WW).2 hy), hvac]
      have e2 : heisO ψ S WW x (heisO ψ S WW y vac) =
          ψ (symplOH S WW x y) • heisO ψ S WW (x + y) vac := heisL_heisL S WW ψ x y vac
      rw [e2]
      refine smul_mem_of_mem (psiH_mem hψ hSd hWd (finX x hx) (finY y hy)) (Submodule.subset_span ⟨x + y, ?_, rfl⟩)
      refine Matrix.ext fun a b => ?_
      have q1 : infPart D (x a b) = 0 := congrFun (congrFun (finX x hx) a) b
      have q2 : infPart D (y a b) = 0 := congrFun (congrFun (finY y hy) a) b
      change infPart D (x a b + y a b) = 0
      rw [RingHom.map_add, q1, q2, add_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
    | smul c f _ hf =>
      change Tm ((c : ℂ) • f) ∈ V
      rw [map_smul]
      exact V.smul_mem c hf
  obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').1 (hT _ hmem)
  choose w hw hgw using fun p => (g p).2
  refine ⟨n, fun p => (f p : ℂ), w, fun p => mem_algebraicClosure_iff.1 (f p).2, hw, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hgw p]
  rfl

theorem finDatum'_isAlgComb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X →
    ∀ t : T, GlobalTheory.MovedAlg.IsAlgComb W.ψ A' WW X.vac' (X.f' t) := by
  intro D T L sc G W i j A A' WW X hX t
  have hI := hX.is
  have hν := (hI.weil' t).hecT
  have he := hI.idem t
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)
  have hSd : IsSelfDualC A' X.rA'.Λ := hI.rigA'.1
  have hWd : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  exact isAlgComb_of_isThetaAt hI.isVac'.1 hSd hWd (by rw [← RingHom.map_mul, hee]) hinf
    (GlobalTheory.CompanionTheory.StdSndTheta.stdSnd_isSB hν.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) _ A' WW X.rA'.β X.rW.β _
      (GlobalTheory.CompanionTheory.StdSndTheta.exists_den_dualCoord hSd.1.fg hWd.1.fg X.rA'.β X.rW.β)
      (GlobalTheory.CompanionTheory.StdSndTheta.exists_mul_dualCoord hSd.1 hWd.1 hinf X.rA'.β X.rW.β))
    (fun x => stdSnd_mem hν.1 he _ _ A' WW X.rA'.β X.rW.β x) (hI.snd t)

end GlobalTheory.BotFourierSnd

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_isAlgebraicCombination_definiteBottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X →
    ∀ t : T, GlobalTheory.MovedAlg.IsAlgComb W.ψ A' WW X.vac' (X.f' t) := by
  atlas_forward_decl GlobalTheory.BotFourierSnd.finDatum'_isAlgComb
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.AlgPair

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem alg_star {a : ℂ} (ha : a ∈ algebraicClosure ℚ ℂ) : star a ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff] at ha ⊢
  exact ha.algHom ((Complex.conjAe.restrictScalars ℚ).toAlgHom)

theorem fin_neg {x : WO S T} (hx : x.map (infPart D) = 0) : (-x).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.zero_apply] at h ⊢
  rw [RingHom.map_neg, h, neg_zero]

theorem fin_add {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  have h' := congrFun (congrFun hy i) j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at h h' ⊢
  rw [RingHom.map_add, h, h', add_zero]

variable {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem thetaInner_zero_left (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 0 G = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_left μ 𝓕 0 0 G
  simpa using h

theorem thetaInner_zero_right (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 G 0 = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_right μ 𝓕 0 G 0
  simpa using h

theorem sum_left (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {G : WO S T → ℂ}
    (hG : IsThetaFunO ψ S T G) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 (∑ p, c p • g p) G = ∑ p, star (c p) * GlobalTheory.RawLift.thetaIP μ 𝓕 (g p) G
  | 0, c, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_left G⟩
  | n + 1, c, g, hg => by
    obtain ⟨ht, he⟩ := sum_left hψ hcv hG (fun p => c p.succ) (fun p => g p.succ) fun p => hg _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_left hψ hcv _ (hg 0) ht hG, he]⟩

theorem sum_right (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 f (∑ p, c p • g p) = ∑ p, c p * GlobalTheory.RawLift.thetaIP μ 𝓕 f (g p)
  | 0, c, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_right f⟩
  | n + 1, c, g, hg => by
    obtain ⟨ht, he⟩ := sum_right hψ hcv hf (fun p => c p.succ) (fun p => g p.succ) fun p => hg _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_right hψ hcv _ hf (hg 0) ht, he]⟩

variable {θ : InfFam D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
  {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {v : WO S T → ℂ}

theorem vac_translate (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {u : WO S T}
    (hu : u.map (infPart D) = 0) : GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have hlat := hv.2.lat
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  by_cases hmem : u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
  · obtain ⟨ε, hε, hεv⟩ := h3 v hlat u hmem
    have hself : GlobalTheory.RawLift.thetaIP μ 𝓕 v v = 1 := by
      rw [GlobalTheory.RawLift.thetaInner_self]
      have hn := hv.2.norm.2 (μ, 𝓕) hcv
      simp only [nrm2] at hn
      rw [hn, Complex.ofReal_one]
    rw [hεv v hlat, GlobalTheory.RawLift.thetaInner_smul_right, hself, mul_one]
    rcases hε with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  · have hne : ∃ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        ψ (symplO S T u u') ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hmem ((h1 u hu).2 hcon)
    obtain ⟨u', hu', hψu⟩ := hne
    obtain ⟨ε, hε, hεv⟩ := h3 v hlat u' hu'
    have hεv' := hεv v hlat
    have comm := GlobalTheory.SplitScalar.heisO_comm ψ S T u u' v
    rw [hεv', GlobalTheory.VacSchurFin.heisO_smul'] at comm
    have inv := GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv hvt (laws.1 u v hvt) u'
    rw [hεv'] at inv
    have hεε : star ε * ε = 1 := by
      rcases hε with h | h <;> rw [h] <;> simp only [star_one, star_neg, one_mul, neg_mul_neg]
    have hfix : ψ (symplO S T u u') * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) =
        GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) := by
      conv_lhs => rw [← inv, ← GlobalTheory.RawLift.thetaInner_smul_right, ← comm, GlobalTheory.RawLift.thetaInner_smul_left,
        GlobalTheory.RawLift.thetaInner_smul_right, ← mul_assoc, hεε, one_mul]
    have h0 : (ψ (symplO S T u u') - 1) * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) = 0 := by
      rw [sub_mul, hfix, one_mul, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hψu)]
    exact zero_mem _

theorem translates (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {x y : WO S T}
    (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    GlobalTheory.RawLift.thetaIP μ 𝓕 (heisO ψ S T x v) (heisO ψ S T y v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have e1 : heisO ψ S T (-x) (heisO ψ S T x v) = ψ (symplOH S T (-x) x) • v := by
    rw [GlobalTheory.SplitScalar.heisO_heisO, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero]
  have e2 : heisO ψ S T (-x) (heisO ψ S T y v) = ψ (symplOH S T (-x) y) • heisO ψ S T (-x + y) v :=
    GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) y v
  rw [← GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv (laws.1 x v hvt) (laws.1 y v hvt) (-x), e1, e2,
    GlobalTheory.RawLift.thetaInner_smul_left, GlobalTheory.RawLift.thetaInner_smul_right]
  refine mul_mem (alg_star (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hx))
    (mul_mem (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hy) ?_)
  exact vac_translate hv hS hT hcv (fin_add (fin_neg hx) hy)

theorem thetaIP_algComb : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F F' : WO S T → ℂ,
    GlobalTheory.MovedAlg.IsAlgComb ψ S T v F → GlobalTheory.MovedAlg.IsAlgComb ψ S T v F' → IsAlgebraic ℚ (GlobalTheory.RawLift.thetaIP μ 𝓕 F F') := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT μ 𝓕 hcv F F' hF hF'
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨m, c', w', hc', hw', rfl⟩ := hF'
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hth : ∀ x, IsThetaFunO ψ S T (heisO ψ S T x v) := fun x => laws.1 x v hvt
  have hR := (sum_right hψ hcv (hth 0) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).1
  rw [(sum_left hψ hcv hR c (fun p => heisO ψ S T (w p) v) fun p => hth _).2, ← mem_algebraicClosure_iff]
  refine Subalgebra.sum_mem _ fun p _ => mul_mem (alg_star (mem_algebraicClosure_iff.2 (hc p))) ?_
  rw [(sum_right hψ hcv (hth (w p)) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).2]
  exact Subalgebra.sum_mem _ fun q _ =>
    mul_mem (mem_algebraicClosure_iff.2 (hc' q)) (translates hv hS hT hcv (hw p) (hw' q))

end GlobalTheory.AlgPair

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_self_dual_lattices : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F F' : WO S T → ℂ,
    GlobalTheory.MovedAlg.IsAlgComb ψ S T v F → GlobalTheory.MovedAlg.IsAlgComb ψ S T v F' → IsAlgebraic ℚ (GlobalTheory.RawLift.thetaIP μ 𝓕 F F') := by
  atlas_forward_decl GlobalTheory.AlgPair.thetaIP_algComb
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotExpand

section Gen

open GlobalTheory.MovedAlg GlobalTheory.AlgWave GlobalTheory.RawLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem vac_ne_zero (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v) :
    v ≠ 0 := by
  rintro rfl
  obtain ⟨p, hp⟩ := hv.2.norm.1
  have := hv.2.norm.2 p hp
  simp [nrm2] at this

theorem alg_self : IsAlgComb ψ S T v v :=
  ⟨1, fun _ => 1, fun _ => 0, fun _ => isAlgebraic_one, fun _ => Matrix.ext fun _ _ => (infPart D).map_zero, by
    simp [GlobalTheory.SplitScalar.heisO_zero]⟩

theorem theta_of_alg (hψ : IsStdChar D ψ (-1)) (hv : IsThetaFunO ψ S T v) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) :
    IsThetaFunO ψ S T F := by
  obtain ⟨n, c, w, -, -, rfl⟩ := hF
  refine Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun p _ => GlobalTheory.OrientedHeis.theta_smul _ ((GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 _ _ hv)

theorem star_mem {a : ℂ} (ha : a ∈ Qb) : star a ∈ Qb :=
  mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 ha).algHom (starRingEnd ℂ).toRatAlgHom)

variable (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
  (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
include hv hS hT

theorem rigid {F F' : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) (hF' : IsAlgComb ψ S T v F') (h0 : F ≠ 0) {c : ℂ}
    (hc : F' = c • F) : IsAlgebraic ℚ c := by
  obtain ⟨p, hp⟩ := hv.2.norm.1
  have h1 := mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp F F hF hF)
  have h2 := mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp F F' hF hF')
  have h3 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hv.1 (theta_of_alg hv.1 hv.2.theta hF) h0 hp
  rw [hc, thetaInner_smul_right] at h2
  have := div_mem h2 h1
  rw [mul_div_cancel_right₀ _ h3] at this
  exact mem_algebraicClosure_iff.1 this

theorem om_scaled (hW : IsWeilDatumO ψ S T χS χT om) {p : GA D S × GA D T} {κ : ℂ} {F₀ : WO S T → ℂ}
    (h0 : IsAlgComb ψ S T v F₀) (hp : om p v = κ • F₀) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) :
    ∃ F₁, IsAlgComb ψ S T v F₁ ∧ om p F = κ • F₁ := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨x, h⟩ := p
  refine ⟨∑ q, c q • heisO ψ S T (actO S T x h (w q)) F₀, IsAlgComb.finsum _ _ hc fun q => IsAlgComb.Heisenberg₂
    (fun a b ha hb => mem_algebraicClosure_iff.1 (GlobalTheory.BotFourier.psiH_mem hv.1 hS hT ha hb))
    (GlobalTheory.FinApprox.actO_fin _ _ (hw q)) h0, ?_⟩
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hW.om_heis x h (w q) v hv.2.theta, hp, GlobalTheory.VacSchurFin.heisO_smul', smul_comm]

theorem om_alg (hW : IsWeilDatumO ψ S T χS χT om) {p : GA D S × GA D T}
    (h0 : IsAlgComb ψ S T v (om p v)) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) : IsAlgComb ψ S T v (om p F) := by
  obtain ⟨F₁, h1, h2⟩ := om_scaled hv hS hT hW (κ := 1) h0 (one_smul _ _).symm hF
  rwa [h2, one_smul]

theorem om_ne_zero (p : GA D S × GA D T) : om p v ≠ 0 := fun h => vac_ne_zero hv (by
  have : om p⁻¹ (om p v) = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, map_zero])

variable (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
  (hW : IsWeilDatumO ψ S T χS χT om)
include hcS hcT hW

theorem root_closed {x : GA D S} (hx : x ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) {m : ℕ} (hm : 0 < m)
    (hp : IsAlgComb ψ S T v (om ((x, h) ^ m) v)) : IsAlgComb ψ S T v (om (x, h) v) := by
  obtain ⟨κ, F, hF, e⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hv hS hT hcS hcT hW x hx h hh
  have key : ∀ k : ℕ, ∃ F₁, IsAlgComb ψ S T v F₁ ∧ om ((x, h) ^ k) v = κ ^ k • F₁ := by
    intro k
    induction k with
    | zero => exact ⟨v, alg_self, by simp⟩
    | succ k ih =>
      obtain ⟨F₁, h1, h2⟩ := ih
      obtain ⟨F₂, h3, h4⟩ := om_scaled hv hS hT hW hF e h1
      exact ⟨F₂, h3, by rw [pow_succ', map_mul, Module.End.mul_apply, h2, map_smul, h4, smul_smul, pow_succ]⟩
  obtain ⟨F₁, h1, h2⟩ := key m
  have h0 : F₁ ≠ 0 := fun h0 => om_ne_zero hv hS hT _ (by rw [h2, h0, smul_zero])
  rw [e]
  exact hF.smul (IsAlgebraic.of_pow hm (rigid hv hS hT h1 hp h0 h2))

def algGroup : Subgroup (GA D S × GA D T) where
  carrier := {p | p.1 ∈ GfC S ∧ p.2 ∈ GfC T ∧ IsAlgComb ψ S T v (om p v)}
  one_mem' := ⟨one_mem _, one_mem _, by rw [map_one]; exact alg_self⟩
  mul_mem' := fun {p q} hp hq => ⟨mul_mem hp.1 hq.1, mul_mem hp.2.1 hq.2.1, by
    rw [map_mul]; exact om_alg hv hS hT hW hp.2.2 hq.2.2⟩
  inv_mem' := fun {p} hp => ⟨inv_mem hp.1, inv_mem hp.2.1, by
    obtain ⟨κ, F, hF, e⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hv hS hT hcS hcT hW _ (inv_mem hp.1) _ (inv_mem hp.2.1)
    have e' : om p⁻¹ v = κ • F := e
    have h1 : v = κ • om p F := by
      rw [← map_smul, ← e', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h0 : om p F ≠ 0 := fun h0 => vac_ne_zero hv (by rw [h1, h0, smul_zero])
    rw [e']
    exact hF.smul (rigid hv hS hT (om_alg hv hS hT hW hp.2.2 hF) alg_self h0 h1)⟩

omit hv hS hT hcS hcT hW in
theorem mem_GfC_of_suppAt {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V}
    (hg : Formalism.L2.Theta.SuppAt e V g) : g ∈ GfC V := by
  have h1 := GlobalTheory.SplitScalar.infPart_splitIdem he
  have h2 := GlobalTheory.PlaceDatum.infPart_cA h1
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  change (Formalism.L2.Theta.mt V g).map (infPart D) = 1
  rw [← sub_eq_zero]
  ext i j
  rw [← GlobalTheory.SplitCharTrivial.map_sub_one, ← hg i j, RingHom.map_mul, RingHom.map_add, h1, h2, add_zero, zero_mul]
  rfl

theorem split_alg {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {g : GA D S} {h : GA D T}
    (hg : Formalism.L2.Theta.SuppAt e S g) (hh : Formalism.L2.Theta.SuppAt e T h) : IsAlgComb ψ S T v (om (g, h) v) := by
  obtain ⟨κ, F, hF, eF⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hv hS hT hcS hcT hW g (mem_GfC_of_suppAt he hg) h (mem_GfC_of_suppAt he hh)
  obtain ⟨x, hx⟩ := GlobalTheory.WeilDetermined.exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := GlobalTheory.WeilDetermined.exists_isDetAt he.1 T h
  obtain ⟨r, hr, hℓ⟩ := hW.om_split e he g h hg hh x y hx hy
  have h1 := GlobalTheory.SplitScalar.infPart_splitIdem he
  have hx1 : infPart D (x : Formalism.L2.Theta.AE D) = 1 := by
    rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, zero_mul, zero_add, sub_zero]
  have hy1 : infPart D (y : Formalism.L2.Theta.AE D) = 1 := by
    rw [hy, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, zero_mul, zero_add, sub_zero]
  have hz : ((splitFacO χS χT x y : Circle) : ℂ) ∈ Qb := by
    rw [splitFacO, Circle.coe_mul, Circle.coe_inv]
    exact mul_mem (inv_mem (mem_algebraicClosure_iff.2 (GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta hv.2.inf hW.hecT hW.resT x hx1)))
      (mem_algebraicClosure_iff.2 (GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta hv.2.inf hW.hecS hW.resS y hy1))
  have hz1 : star ((splitFacO χS χT x y : Circle) : ℂ) * (splitFacO χS χT x y : Circle) = 1 := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  generalize ((splitFacO χS χT x y : Circle) : ℂ) = z at hℓ hz hz1

  obtain ⟨p, hp⟩ := hv.2.norm.1
  have hF0 : F ≠ 0 := fun h0 => om_ne_zero hv hS hT _ (by rw [eF, h0, smul_zero])
  have n1 := GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om p.1 p.2 hW hp (g, h) v v hv.2.theta hv.2.theta
  rw [eF, thetaInner_smul_left, thetaInner_smul_right, ← mul_assoc] at n1
  have n2 : star κ * κ ∈ Qb := by
    rw [eq_div_of_mul_eq (GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hv.1 (theta_of_alg hv.1 hv.2.theta hF) hF0 hp) n1]
    exact div_mem (mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp v v alg_self alg_self))
      (mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp F F hF hF))

  obtain ⟨n, c, w, hc, hw, hFe⟩ := id hF
  obtain ⟨ℓ, l1, l2, l3⟩ := GlobalTheory.T.exists_algebraicInvariantForm_vacuum_splitPlace hv hS hT e he n w hw
  have ha : ℓ F ∈ Qb := by
    rw [hFe, map_sum]
    exact sum_mem fun q _ => by
      rw [map_smul, smul_eq_mul]
      exact mul_mem (mem_algebraicClosure_iff.2 (hc q)) (mem_algebraicClosure_iff.2 (l3 q))
  have e1 := hℓ ℓ l1 v hv.2.theta
  rw [eF, map_smul, smul_eq_mul, l2, mul_one] at e1
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hz0 : z ≠ 0 := right_ne_zero_of_mul_eq_one hz1
  have ha0 : ℓ F ≠ 0 := fun h0 => mul_ne_zero hr0 hz0 (by rw [← e1, h0, mul_zero])
  have e2 : (r : ℂ) ^ 2 = (star κ * κ) * (star (ℓ F) * ℓ F) := by
    have e3 := congrArg star e1
    rw [star_mul', star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def] at e3
    linear_combination (-(r : ℂ) ^ 2) * hz1 - (star κ * star (ℓ F)) * e1 - (r * z) * e3
  have hrq : (r : ℂ) ∈ Qb := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.1
    (e2 ▸ mul_mem n2 (mul_mem (star_mem ha) ha))))
  have hκ : κ ∈ Qb := by
    rw [eq_div_of_mul_eq ha0 e1]
    exact div_mem (mul_mem hrq hz) ha
  rw [eF]
  exact hF.smul (mem_algebraicClosure_iff.1 hκ)

omit hv hS hT hcS hcT hW in
theorem finCong_one (V : HSp D) (N : ℕ) : GlobalTheory.Member.FinCong V N 1 := by
  have h := (GlobalTheory.Member.PrincLevel.levelGroup V N).one_mem
  exact h.2

theorem mem_algGroup {p : GA D S × GA D T} :
    p ∈ algGroup hv hS hT hcS hcT hW ↔ p.1 ∈ GfC S ∧ p.2 ∈ GfC T ∧ IsAlgComb ψ S T v (om p v) := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem source_mem {x : GA D S} (hx : x ∈ GfC S) : (x, (1 : GA D T)) ∈ algGroup hv hS hT hcS hcT hW := by
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.congruent_pairs_fix_vacuum_weilDatum hv hS hT hcS hcT hW
  refine GlobalTheory.T.finiteUnitaryPoints_mem_of_level_and_split_place S ((algGroup hv hS hT hcS hcT hW).comap (MonoidHom.inl _ _)) N hN (fun g hg m hm hp => ?_)
    (fun k hk hc => ?_) (fun e he g hg => ?_) x hx
  · rw [Subgroup.mem_comap, map_pow, mem_algGroup] at hp
    rw [Subgroup.mem_comap, MonoidHom.inl_apply, mem_algGroup]
    exact ⟨hg, one_mem _, root_closed hv hS hT hcS hcT hW hg (one_mem _) hm hp.2.2⟩
  · rw [Subgroup.mem_comap, MonoidHom.inl_apply, mem_algGroup, hlev k hk 1 (one_mem _) hc (finCong_one T N)]
    exact ⟨hk, one_mem _, alg_self⟩
  · rw [Subgroup.mem_comap, MonoidHom.inl_apply, mem_algGroup]
    exact ⟨mem_GfC_of_suppAt he hg, one_mem _,
      split_alg hv hS hT hcS hcT hW he hg (GlobalTheory.WeilDetermined.suppAt_one e T)⟩

set_option maxHeartbeats 1000000 in
theorem target_mem {h : GA D T} (hh : h ∈ GfC T) : ((1 : GA D S), h) ∈ algGroup hv hS hT hcS hcT hW := by
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.congruent_pairs_fix_vacuum_weilDatum hv hS hT hcS hcT hW
  refine GlobalTheory.T.finiteUnitaryPoints_mem_of_level_and_split_place T ((algGroup hv hS hT hcS hcT hW).comap (MonoidHom.inr _ _)) N hN (fun g hg m hm hp => ?_)
    (fun k hk hc => ?_) (fun e he g hg => ?_) h hh
  · rw [Subgroup.mem_comap, map_pow, mem_algGroup] at hp
    rw [Subgroup.mem_comap, MonoidHom.inr_apply, mem_algGroup]
    exact ⟨one_mem _, hg, root_closed hv hS hT hcS hcT hW (one_mem _) hg hm hp.2.2⟩
  · rw [Subgroup.mem_comap, MonoidHom.inr_apply, mem_algGroup, hlev 1 (one_mem _) k hk (finCong_one S N) hc]
    exact ⟨one_mem _, hk, alg_self⟩
  · rw [Subgroup.mem_comap, MonoidHom.inr_apply, mem_algGroup]
    exact ⟨one_mem _, mem_GfC_of_suppAt he hg,
      split_alg hv hS hT hcS hcT hW he (GlobalTheory.WeilDetermined.suppAt_one e S) hg⟩

theorem om_vac_algComb {x : GA D S} (hx : x ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) :
    IsAlgComb ψ S T v (om (x, h) v) := by
  have h3 := (algGroup hv hS hT hcS hcT hW).mul_mem (source_mem hv hS hT hcS hcT hW hx)
    (target_mem hv hS hT hcS hcT hW hh)
  rw [Prod.mk_mul_mk, mul_one, one_mul, mem_algGroup] at h3
  exact h3.2.2

end Gen

theorem ker'_eq_sum_jets : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X →
    ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∃ (k : ℕ) (c : Fin k → ℂ) (w : Fin k → WO A' WW),
      (∀ l, IsAlgebraic ℚ (c l)) ∧ (∀ l, (w l).map (infPart D) = 0) ∧
      (∀ l, ∃ m : ℕ, 0 < m ∧ m • w l ∈ latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) ∧
      ∀ P : PolF D WW.rank A'.rank, X.ker' W.ψ W.θ t P h x =
        ∑ l, c l * pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (heisO W.ψ A' WW (w l) X.vac') P 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t x hx h hh
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  have hv : IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ X.vac' := hX.is.isVac'
  have hθ : IsInfFam W.θ := hv.2.inf
  have hS : IsSelfDualC A' X.rA'.Λ := hX.is.rigA'.1
  have hT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hf := GlobalTheory.T.finiteDatum_isAlgebraicCombination_definiteBottom hX t
  obtain ⟨k, c, w, hc, hw, e⟩ := om_alg hv hS hT hW (om_vac_algComb hv hS hT (fun τ => (hX.is.rigA'.2.2 τ).1)
    (fun τ => (hX.is.rigW.2.2 τ).1) hW hx hh) hf
  refine ⟨k, c, w, hc, hw, fun l => GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 _ (hw l), fun P => ?_⟩
  have e1 := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW _ _ (X.ω' t) hW hθ X.rA'.s X.rA'.s X.rA'.B X.rA'.B
    X.rW.s X.rW.s X.rW.B X.rW.B x h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hx, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hh, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hx, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hh, Matrix.one_mul]) (X.f' t)
    (theta_of_alg hv.1 hv.2.theta hf) P).2
  have e2 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ A' WW hv.1 hθ X.rA'.s X.rW.s X.rA'.B X.rW.B X.vac'
    hv.2.theta k c w hw P).1
  have ft := (GlobalTheory.FinTranslate.finite_translate D W.ψ W.θ A' WW hv.1 hθ X.vac' hv.2.theta).2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker' thetaKO
  rw [e1, e, ← e2, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(ft (w l) (hw l)).2, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.BotExpand

end
end
