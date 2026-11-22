module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilRepresentationExists
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.PrimesInProgressionNonempty
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.MovedField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.FunObj Formalism.L2.Host ValuativeRel

variable {D : D7}

theorem exists_zpow_unit (w : Pl D.host.E) (x : (Kw w)ˣ) :
    ∃ n : ℤ, Valued.v (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := by
  have h0 : Valued.v (x : Kw w) ≠ 0 := by simp
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx : Valued.v (x : Kw w) = WithZero.exp (WithZero.log (Valued.v (x : Kw w))) := (WithZero.exp_log h0).symm
  refine ⟨WithZero.log (Valued.v (x : Kw w)), ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, hu, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  simp

theorem natCast_cpow_half (N : ℕ) (m : ℤ) :
    (N : ℂ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N : ℝ) : ℂ) ^ m := by
  rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

theorem sqrt_absNorm_ne_zero (w : Pl D.host.E) : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ≠ 0 := by
  have h : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)
  exact_mod_cast (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)))

theorem apow_half_mem {w : Pl D.host.E} {K : Subfield ℂ}
    (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) (z : ℤ) : apow x ((z : ℂ) / 2) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have h1 : valuation (Kw w) (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := (Good.isEquiv_Kw w).eq_one_iff_eq_one.2 hn
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, apow_mul, apow_of_valuation_eq_one h1, one_mul, apow_zpow, (isUnif_unifAt w).apow_eq,
    GlobalTheory.LFun.SatBoundGL.resCard_completion]
  have e1 : -(((-n : ℤ) : ℂ) * ((z : ℂ) / 2)) = ((((n * z : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, natCast_cpow_half]
  exact zpow_mem hs _

theorem loc_mem_of_unrAt {w : Pl D.host.E} {K : Subfield ℂ} {χ : HChar D.host.E} (hu : χ.UnrAt w)
    (hv : χ.valTw (1 / 2) w ∈ K) (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) :
    ((χ.loc w x : ℂˣ) : ℂ) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, map_mul, hu _ hn, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  refine zpow_mem ?_ _
  have e1 : -(((1 / 2 : ℝ)) : ℂ) = ((((-1 : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hval : χ.valTw (1 / 2) w = ((χ.loc w (unifAt w) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)⁻¹ := by
    rw [HChar.valTw, e1, natCast_cpow_half, zpow_neg_one]
    rfl
  have : ((χ.loc w (unifAt w) : ℂˣ) : ℂ) = χ.valTw (1 / 2) w * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) := by
    rw [hval, inv_mul_cancel_right₀ (sqrt_absNorm_ne_zero w)]
  rw [this]
  exact mul_mem hv hs

theorem units_prod_mem {α : Type*} (K : Subfield ℂ) (f : α → ℂˣ) :
    ∀ l : List α, (∀ a ∈ l, ((f a : ℂˣ) : ℂ) ∈ K) → (((l.map f).prod : ℂˣ) : ℂ) ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons, Units.val_mul]
    exact mul_mem (h a List.mem_cons_self) (units_prod_mem K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem list_prod_mem' {α : Type*} (K : Subfield ℂ) (f : α → ℂ) :
    ∀ l : List α, (∀ a ∈ l, f a ∈ K) → (l.map f).prod ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (h a List.mem_cons_self) (list_prod_mem' K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

end GlobalTheory.MovedField

