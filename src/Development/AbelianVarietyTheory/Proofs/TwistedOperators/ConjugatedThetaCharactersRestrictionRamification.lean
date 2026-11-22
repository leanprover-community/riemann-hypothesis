module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueCharStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifiStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart
public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSplitChars
open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E]

theorem twVal_of_unit (χ : HChar E) (w : ℝ) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) (hk : P.valuation E (k : E) = 1) :
    twVal χ w P k = ((χ.locK P k : ℂˣ) : ℂ) := by
  have h0 : Formalism.L2.Host.ordF P k = 0 := by simp [Formalism.L2.Host.ordF, hk]
  simp [twVal, h0]

theorem isClopen_oneUnits (P : HeightOneSpectrum (𝓞 E)) :
    IsClopen {x : (P.adicCompletion E)ˣ | Valued.v ((x : P.adicCompletion E) - 1) < 1} := by
  have := (Valued.isClopen_ball (P.adicCompletion E) (r := 1)).preimage
      (f := fun x : (P.adicCompletion E)ˣ => (x : P.adicCompletion E) - 1)
      ((Units.continuous_val (M := P.adicCompletion E)).sub continuous_const)
  convert this using 1
  ext x
  simp

theorem tameAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E ((u : E) - 1) < 1 → χ.locK P u = 1) : χ.TameAt P := by
  have key : ∀ x : (P.adicCompletion E)ˣ, Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1 := by
    intro x
    refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on
      (p := fun x => Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1) x ?_ fun k hk => h k ?_
    · exact isClosed_imp (isClopen_oneUnits P).2
        (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)
    · have e : ((atFin P k : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1 =
          algebraMap E (P.adicCompletion E) ((k : E) - 1) := by
        rw [map_sub, map_one]; rfl
      rwa [e, Formalism.UG.P.levelaf_valued_algebraMap] at hk
  intro x _ hx
  refine key x (lt_of_le_of_lt hx ?_)
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.2 (by norm_num)

theorem locK_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ)
    (hk : P.valuation E (k : E) = 1) : ((χ'.locK P k : ℂˣ) : ℂ) = s ((χ.locK P k : ℂˣ) : ℂ) := by
  have := h P k
  rwa [twVal_of_unit _ _ _ _ hk, twVal_of_unit _ _ _ _ hk] at this

theorem unrAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (hu : χ.UnrAt P) : χ'.UnrAt P :=
  GlobalTheory.EtaConjType.unrAt_of_locK χ' P fun u hu' => Units.ext (by
    rw [locK_conj h P u hu', GlobalTheory.NormOneUnit.locK_unr hu hu', Units.val_one, map_one])

theorem tameAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (ht : χ.TameAt P) : χ'.TameAt P := by
  refine tameAt_of_locK χ' P fun u hu => Units.ext ?_
  have h1 : P.valuation E ((1 : Eˣ) : E) = 1 := by simp
  have hu1 : P.valuation E (u : E) = 1 := by
    have := Valuation.map_eq_of_sub_lt (P.valuation E) (x := 1) (y := (u : E)) (by rwa [map_one])
    rwa [map_one] at this
  rw [locK_conj h P u hu1, GlobalTheory.NormOneUnit.locK_tame ht h1 (by simpa using hu), map_one, Units.val_one, map_one]

end GlobalTheory.ConjSplitChars

end
