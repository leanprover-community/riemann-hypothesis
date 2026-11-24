module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import GroundTheory.PAdicHodge.WAKummerEps
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT
public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.TieQB
public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic
public import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonFromAlternative
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
public import GroundTheory.PAdicHodge.BCrisEigen
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InvRestrictScalarsMem
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.PAdicHodge.BdRTGalois
import Mathlib.Algebra.Order.Star.Real
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import GroundTheory.PAdicHodge.ACrisFrobFixed
import GroundTheory.PAdicHodge.BCrisPlusInvariants
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Polynomial.Basic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.CoeUntiltIterateLFlat, Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta, Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsCoeEqUntiltPFlat, Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.BasedP, Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.ABInjective, Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.CoeffLMul, Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.BaseAinfPlus, Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero, Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.ThetaAlgebraMap.ThAlgebraMap, Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.BaseFixed, Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.Base

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.CoeUntiltIterateLFlat =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.CoeUntiltIterateLFlat", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT\npublic import GroundTheory.PAdicHodge.WAKummerEps\npublic import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6\npublic import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GroundTheory.PAdicHodge

namespace UpperTheory.Lit.Drps.Kum

variable {l : ℕ} [Fact l.Prime]

local notation "𝒪" => normInteger ℂ_[l]
local notation "𝒪♭" => PreTilt 𝒪 l
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv 𝒪♭ l)

variable {P : Formalism.BasicNotions.LocPrime l} (AI : Formalism.BasicNotions.LocAinf l P)

def zeta (n : ℕ) : 𝒪 := Formalism.Per6.intEquiv l (AI.ζ n)

theorem zeta_succ (n : ℕ) : zeta AI (n + 1) ^ l = zeta AI n := by
  rw [zeta, ← map_pow, AI.ζ_succ]; rfl

def epsT : 𝒪♭ := IsPerfectoidField.ofCompatible l (zeta AI) (zeta_succ AI)

theorem tiltMap_eps : Formalism.Per6.tiltMap l AI.ε = epsT AI :=
  IsPerfectoidField.preTilt_ext l fun n => by
    rw [epsT, IsPerfectoidField.coeff_ofCompatible, Formalism.Per6.tiltMap]
    show (Formalism.Per6.modPEquiv l) (PreTilt.coeff n AI.ε) = _
    rw [AI.ε_coeff]
    rfl

theorem untilt_epsT : PreTilt.untilt (epsT AI) = 1 := by
  rw [epsT, IsPerfectoidField.untilt_ofCompatible, zeta, AI.ζ_zero, map_one]

theorem coe_pow' (x : PadicAlgCl l) (n : ℕ) : ((x ^ n : PadicAlgCl l) : ℂ_[l]) = (x : ℂ_[l]) ^ n :=
  map_pow (UniformSpace.Completion.coeRingHom (α := PadicAlgCl l)) x n

theorem norm_lRoot_le (m : ℕ) : ‖((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l])‖ ≤ 1 := by
  have h : ‖((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l])‖ ^ (l ^ m) = ‖(((l : PadicAlgCl l)) : ℂ_[l])‖ := by
    rw [← norm_pow, ← coe_pow', GlobalTheory.Pst.lRoot_pow l m]
  have hl : ‖(((l : PadicAlgCl l)) : ℂ_[l])‖ ≤ 1 := by
    have := (IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) (p := l)).le
    simpa using this
  rw [← h] at hl
  by_contra hlt
  push_neg at hlt
  exact absurd hl (not_le.2 (one_lt_pow₀ hlt (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)))

def lRootInt (m : ℕ) : 𝒪 := ⟨((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l]), mem_normInteger.2 (norm_lRoot_le m)⟩

theorem lRootInt_succ (m : ℕ) : lRootInt (l := l) (m + 1) ^ l = lRootInt m :=
  Subtype.ext (by
    show ((GlobalTheory.Pst.lRoot l (m + 1) : PadicAlgCl l) : ℂ_[l]) ^ l = ((GlobalTheory.Pst.lRoot l m : PadicAlgCl l) : ℂ_[l])
    rw [← GlobalTheory.Pst.lRoot_succ l m, coe_pow'])


variable (l) in
def lFlat : 𝒪♭ := IsPerfectoidField.ofCompatible l lRootInt lRootInt_succ

theorem coe_untilt_iterate_lFlat (n : ℕ) :
    ((PreTilt.untilt (φi^[n] (lFlat l)) : 𝒪) : ℂ_[l]) = ((GlobalTheory.Pst.lRoot l n : PadicAlgCl l) : ℂ_[l]) := by
  rw [lFlat, untilt_iterate_ofCompatible]; rfl

theorem iterate_mul (n : ℕ) (x y : 𝒪♭) : φi^[n] (x * y) = φi^[n] x * φi^[n] y :=
  by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem coe_untilt_mul (x y : 𝒪♭) :
    ((PreTilt.untilt (x * y) : 𝒪) : ℂ_[l]) = ((PreTilt.untilt x : 𝒪) : ℂ_[l]) * ((PreTilt.untilt y : 𝒪) : ℂ_[l]) := by
  rw [map_mul]; rfl

theorem coe_untilt_iterate_epsT (n : ℕ) :
    ((PreTilt.untilt (φi^[n] (epsT AI)) : 𝒪) : ℂ_[l]) = ((P.ζQ n : PadicAlgCl l) : ℂ_[l]) := by
  rw [epsT, untilt_iterate_ofCompatible, zeta]
  exact AI.ζ_eq n

theorem tiltGal_lFlat (g : Formalism.BasicNotions.Loc.GQ l) :
    tiltGal (Formalism.Per6.toBot g) (lFlat l) = lFlat l * epsPow (untilt_epsT AI) (GlobalTheory.Pst.kummer P g) := by
  refine tilt_ext_untilt fun n => Subtype.ext ?_
  show ((PreTilt.untilt (φi^[n] (tiltGal (Formalism.Per6.toBot g) (lFlat l))) : 𝒪) : ℂ_[l]) =
    ((PreTilt.untilt (φi^[n] (lFlat l * epsPow (untilt_epsT AI) (GlobalTheory.Pst.kummer P g))) : 𝒪) : ℂ_[l])
  rw [coe_untilt_iterate_tiltGal, coe_untilt_iterate_lFlat, iterate_mul, coe_untilt_mul, coe_untilt_iterate_lFlat,
    untilt_iterate_epsPow, SubmonoidClass.coe_pow, coe_untilt_iterate_epsT, gal_smul_coe]
  show (((g (GlobalTheory.Pst.lRoot l n) : PadicAlgCl l)) : ℂ_[l]) = _
  rw [GlobalTheory.Pst.isKummer_kummer P g n, mul_comm]
  push_cast [coe_pow']
  rfl

theorem untilt_lFlat : ((PreTilt.untilt (lFlat l) : 𝒪) : ℂ_[l]) = l := by
  have := coe_untilt_iterate_lFlat (l := l) 0
  rw [Function.iterate_zero_apply] at this
  rw [this, GlobalTheory.Pst.lRoot_zero]
  norm_cast

theorem exists_lFlat_eq : ∃ b : ℤ_[l], lFlat l = pFlat l * epsPow untilt_epsilon b := by
  obtain ⟨η, hη⟩ : pFlat l ∣ lFlat l :=
    preTilt_dvd_iff_norm_le.2 (le_of_eq (by rw [preTilt_norm_def, preTilt_norm_def, untilt_lFlat, coe_untilt_pFlat]))
  have hη1 : PreTilt.untilt η = 1 := by
    have h := congrArg (fun y => ((PreTilt.untilt y : 𝒪) : ℂ_[l])) hη
    rw [coe_untilt_mul, untilt_lFlat, coe_untilt_pFlat] at h
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    exact ((mul_eq_left₀ natCast_p_ne_zero_cp).1 h.symm)
  obtain ⟨b, hb⟩ := exists_epsPow_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one hη1
  exact ⟨b, by rw [hη, hb]⟩

theorem exists_epsT_eq : ∃ a : ℤ_[l], epsPow untilt_epsilon a = epsT AI :=
  exists_epsPow_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (untilt_epsT AI)

theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {m : ℕ} (h : x ^ m = 1) (k : ℕ) : x ^ (k % m) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k m, pow_add, pow_mul, h, one_pow, mul_one]

theorem epsPow_epsPow {a : ℤ_[l]} (ha : epsPow untilt_epsilon a = epsT AI) (c : ℤ_[l]) :
    epsPow (untilt_epsT AI) c = epsPow untilt_epsilon (a * c) := by
  refine tilt_ext_untilt fun n => ?_
  have e1 : PreTilt.untilt (φi^[n] (epsT AI)) =
      PreTilt.untilt (φi^[n] (epsilon l)) ^ (PadicInt.toZModPow n a).val := by
    rw [← ha]; exact untilt_iterate_epsPow _ a n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have e2 : (PadicInt.toZModPow n (a * c)).val = (PadicInt.toZModPow n a).val * (PadicInt.toZModPow n c).val % (l ^ n) := by
    rw [map_mul, ZMod.val_mul]
  have L := untilt_iterate_epsPow (untilt_epsT AI) c n
  have R := untilt_iterate_epsPow (untilt_epsilon (p := l)) (a * c) n
  rw [L, R, e1, ← pow_mul, e2, pow_mod_of_pow_eq_one (untilt_iterate_pow_eq_one (untilt_epsilon (p := l)) n)]

theorem kummer_rel {a b : ℤ_[l]} (ha : epsPow untilt_epsilon a = epsT AI) (hb : lFlat l = pFlat l * epsPow untilt_epsilon b)
    (g : Formalism.BasicNotions.Loc.GQ l) :
    kummerC untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (Formalism.Per6.toBot g) +
      (cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]) * b = b + a * GlobalTheory.Pst.kummer P g := by
  apply epsPow_injective untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one
  apply tilt_mul_left_cancel (pFlat_ne_zero (p := l))
  have h1 := tiltGal_lFlat AI g
  have hp : tiltGal (Formalism.Per6.toBot g) (pFlat l) = pFlat l * kummerEta (Formalism.Per6.toBot g) :=
    pFlat_mul_kummerEta (Formalism.Per6.toBot g)
  rw [hb, map_mul, hp, tiltGal_epsPow, epsPow_epsPow AI ha,
    kummerEta_eq_epsPow untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one, mul_assoc, mul_assoc,
    ← epsPow_add, ← epsPow_add] at h1
  exact h1

theorem exists_rel (T : Formalism.BasicNotions.LocTied6 l P AI) : ∃ a b : ℤ_[l],
    T.eD (P.ιB P.tB) = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)
      (algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a : ℚ_[l]) * fontaineT (epsilon l) untilt_epsilon) ∧
    ∀ g : Formalism.BasicNotions.Loc.GQ l,
      kummerC untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (Formalism.Per6.toBot g) +
        (cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]) * b = b + a * GlobalTheory.Pst.kummer P g := by
  obtain ⟨a, ha⟩ := exists_epsT_eq AI
  obtain ⟨b, hb⟩ := exists_lFlat_eq (l := l)
  refine ⟨a, b, ?_, kummer_rel AI ha hb⟩
  rw [PositivityTheory.LocInh.tie_t T, ← fontaineT_epsPow,
    _root_.GroundTheory.PAdicHodge.fontaineT_congr ((tiltMap_eps AI).trans ha.symm) _ (untilt_epsPow _ a)]

end UpperTheory.Lit.Drps.Kum
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.CoeUntiltIterateLFlat =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT\npublic import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.CoeUntiltIterateLFlat\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.TieQB\nimport Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace UpperTheory.Lit.Drps

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem exists_beta (T : LocTied6 l P AI) : ∃ β : ℚ_[l], ∀ g : GQ l,
    T.eB ((GlobalTheory.Pst.kummer P g : ℚ_[l]) • P.tB) =
      period_ring_base.qB l (period_ring_base.κ g) * period_ring_base.t l +
        (period_ring_base.σB g (period_ring_base.qB l β * period_ring_base.t l) - period_ring_base.qB l β * period_ring_base.t l) := by
  obtain ⟨a, b, ht, hr⟩ := Kum.exists_rel AI T
  have h1 : T.eB P.tB = period_ring_base.qB l (a : ℚ_[l]) * period_ring_base.t l := by
    apply period_ring_base.base_ι_inj l
    rw [map_mul, period_ring_base.base_ι_q, period_ring_base.period_image_eq, period_ring_base.BaseA.ι_eq, ← PositivityTheory.LocInh.tie_ι T, ht, map_mul,
      DeRhamTwist.Twist.tQ_eq]
    rfl
  refine ⟨(b : ℚ_[l]), fun g => ?_⟩
  have h2 : period_ring_base.κ g + period_ring_base.χ g * (b : ℚ_[l]) = b + a * (GlobalTheory.Pst.kummer P g : ℚ_[l]) := by
    have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) (hr g)
    simp only [PadicInt.coe_add, PadicInt.coe_mul] at this
    exact this
  have h3 := congrArg (period_ring_base.qB l) h2
  simp only [map_add (f := _), map_mul] at h3
  rw [Algebra.smul_def, map_mul, period_ring_base.DualB.tie_qB T, h1, map_mul, period_ring_base.base_σ_q, period_ring_base.galois_period_cyclotomic]
  linear_combination (-(period_ring_base.t l)) * h3

end UpperTheory.Lit.Drps
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsCoeEqUntiltPFlat =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsCoeEqUntiltPFlat", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification\nimport GroundTheory.PAdicHodge.BdRTGalois\npublic import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

section cont

variable {l : ℕ} [Fact l.Prime]

local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l)

theorem exists_coe_eq_untilt_pFlat (m : ℕ) : ∃ z : PadicAlgCl l,
    (z : ℂ_[l]) = ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) := by
  have hN : l ^ m ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (l : PadicAlgCl l) (Nat.pos_of_ne_zero hN)
  have hπ : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ^ l ^ m = (l : ℂ_[l]) := by
    rw [← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, coe_untilt_pFlat]
  have hyl : algebraMap (PadicAlgCl l) ℂ_[l] y ^ l ^ m = (l : ℂ_[l]) := by
    rw [← map_pow, hy, map_natCast]
  have hy0 : algebraMap (PadicAlgCl l) ℂ_[l] y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN] at hyl
    exact natCast_p_ne_zero_cp (p := l) hyl.symm
  obtain ⟨w, hw⟩ := exists_coe_eq_of_pow_eq_one hN
    (x := ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) * (algebraMap (PadicAlgCl l) ℂ_[l] y)⁻¹)
    (by rw [mul_pow, inv_pow, hπ, hyl, mul_inv_cancel₀ (natCast_p_ne_zero_cp (p := l))])
  refine ⟨y * w, ?_⟩
  change algebraMap (PadicAlgCl l) ℂ_[l] (y * w) = _
  rw [map_mul, show algebraMap (PadicAlgCl l) ℂ_[l] w = _ from hw, mul_comm, mul_assoc, inv_mul_cancel₀ hy0,
    mul_one]

theorem toZModPow_kummerC_eq (m : ℕ) {g h : GQ l} {z : PadicAlgCl l}
    (hz : (z : ℂ_[l]) = ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l])) (hgh : h z = g z) :
    PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot h)) =
      PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g)) := by
  have e : ∀ σ : GQ l, (toBot σ) • ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) =
      ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) *
        ((PreTilt.untilt (φi^[m] (epsilon l)) : normInteger ℂ_[l]) : ℂ_[l]) ^
          (PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one
            (toBot σ))).val := fun σ =>
    gal_smul_untilt_iterate_of_eq_mul untilt_epsilon
      (tiltGal_eq_mul_epsPow untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one pFlat_ne_zero
        gal_smul_coe_untilt_pFlat (toBot σ)) m
  have hs : ∀ σ : GQ l, (toBot σ) • ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) =
      ((σ z : PadicAlgCl l) : ℂ_[l]) := fun σ => by
    rw [← hz, ← galCp_apply, galCp_coe]
    rfl
  have hπ0 : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ≠ 0 := by
    intro h0
    have hπ : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ^ l ^ m = (l : ℂ_[l]) := by
      rw [← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, coe_untilt_pFlat]
    rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hπ
    exact natCast_p_ne_zero_cp (p := l) hπ.symm
  have h2 := (e h).symm.trans ((hs h).trans (hgh ▸ (hs g).symm |>.trans (e g)))
  have h3 := mul_left_cancel₀ hπ0 h2
  have hprim : IsPrimitiveRoot ((PreTilt.untilt (φi^[m] (epsilon l)) : normInteger ℂ_[l]) : ℂ_[l]) (l ^ m) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.2
      (isPrimitiveRoot_untilt_iterate untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one m)
  exact ZMod.val_injective _ (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

end cont

theorem continuous_κ (l : ℕ) [Fact l.Prime] : Continuous (κ : GQ l → ℚ_[l]) := by
  have hc : Continuous fun g : GQ l =>
      kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g) := by
    refine continuous_iff_continuousAt.2 fun g0 => Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l))
    obtain ⟨z, hz⟩ := exists_coe_eq_untilt_pFlat (l := l) m
    have : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    have hU : IsOpen {h : GQ l | g0⁻¹ * h ∈ (IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup} :=
      (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const_mul _)
    have h1 : g0 ∈ {h : GQ l | g0⁻¹ * h ∈ (IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup} := by
      simp only [Set.mem_ofPred_eq, inv_mul_cancel]
      exact Subgroup.one_mem _
    filter_upwards [hU.mem_nhds h1] with h hh
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh z (IntermediateField.mem_adjoin_simple_self _ _)
    have hgh : h z = g0 z := by
      have := congrArg g0 hfix
      simpa using this
    have e := toZModPow_kummerC_eq m hz hgh
    rw [dist_eq_norm]
    have hmem : kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot h) -
        kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g0) ∈
          Ideal.span {(l : ℤ_[l]) ^ m} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, e, sub_self]
    calc _ ≤ (l : ℝ) ^ (-(m : ℤ)) := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hmem
      _ = (l : ℝ)⁻¹ ^ m := by rw [_root_.zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hm
  exact continuous_subtype_val.comp hc

end period_ring_base
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsCoeEqUntiltPFlat =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.BasedP =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.BasedP", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsCoeEqUntiltPFlat\npublic import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6\npublic import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonFromAlternative\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT\nimport Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.TieQB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace period_ring_base

open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

theorem base_no_kummer (l : ℕ) [Fact l.Prime] : ∀ L : Fld l, FiniteDimensional ℚ_[l] L → ∀ x : B l,
    ¬ ∀ σ ∈ L.fixingSubgroup, σB σ x - x = qB l (κ σ) * t l := by
  intro L hL x h
  obtain ⟨P, AI, ⟨T0⟩⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  obtain ⟨T⟩ := _root_.Formalism.BasicNotions.CmpTie.locTied6_F l P AI ⟨T0⟩
  obtain ⟨β, hβ⟩ := UpperTheory.Lit.Drps.exists_beta T
  have := GlobalTheory.Pst.nontrivial_B P
  apply GlobalTheory.Pst.StLat.kummer_not_frac l P AI T0 ⟨L, hL⟩ 1 (T.eB.symm (x + qB l β * t l)) one_ne_zero
  intro g hg
  apply T.eB.injective
  rw [map_one, one_mul, one_mul, one_mul, one_mul, map_sub, DualB.tie_σB T, RingEquiv.apply_symm_apply, hβ, map_add (f := _),
    ← h g hg]
  ring

end period_ring_base
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.BasedP =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.ABInjective =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.ABInjective", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification\npublic import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective\nimport Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

namespace BaseC

theorem inv_uniq {R : Type*} [CommRing R] {a b c : R} (ha : a * c = 1) (hb : b * c = 1) : a = b :=
  calc a = a * (b * c) := by rw [hb, mul_one]
    _ = (a * c) * b := by ring
    _ = b := by rw [ha, one_mul]

variable {l : ℕ} [Fact l.Prime]

theorem aB_ainfMap (a : WittVector l (PreTilt ↥(PadicComplexInt l) l)) :
    aB l (ainfMap l a) = Formalism.Per6.aB l a := rfl

theorem aB_injective : Function.Injective (aB l) := by
  intro a b h
  obtain ⟨a, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) a
  obtain ⟨b, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) b
  rw [aB_ainfMap, aB_ainfMap] at h
  rw [PositivityTheory.LocInh.aB_injective h]

theorem φ_aB (a : AInf ℂ_[l] l) : φ l (aB l a) = aB l (WittVector.frobenius a) := by
  obtain ⟨b, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) a
  rw [← PositivityTheory.LocInh.frob_ainfMap_frobenius, aB_ainfMap, aB_ainfMap]
  exact (PositivityTheory.LocInh.aB_frobenius b).symm

theorem σ_aB (g : GQ l) (a : AInf ℂ_[l] l) : ∃ a' : AInf ℂ_[l] l, σB g (aB l a) = aB l a' := by
  obtain ⟨b, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) a
  refine ⟨ainfMap l (WittVector.map (PositivityTheory.LocInh.galT g) b), ?_⟩
  rw [aB_ainfMap, aB_ainfMap]
  exact (PositivityTheory.LocInh.aB_act g b).symm

abbrev u (l : ℕ) [Fact l.Prime] : B l := qB l ((l : ℚ_[l])⁻¹)

theorem u_mul : u l * (l : B l) = 1 := by
  rw [u, ← map_natCast (qB l) l, ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), map_one]

theorem map_u (f : B l →+* B l) : f (u l) = u l := by
  refine inv_uniq (c := (l : B l)) ?_ u_mul
  rw [← map_natCast f l, ← map_mul, u_mul, map_one]

theorem aB_mem (a : AInf ℂ_[l] l) : aB l a ∈ Ainf' l :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem u_mem : u l ∈ Ainf' l :=
  Subring.subset_closure (Or.inr rfl)

theorem map_mem {f : B l →+* B l} (h1 : ∀ a, f (aB l a) ∈ Ainf' l) :
    ∀ x ∈ Ainf' l, f x ∈ Ainf' l := fun x hx =>
  (Subring.closure_le (t := (Ainf' l).comap f)).2 (by
    rintro y (⟨a, rfl⟩ | hy)
    · exact h1 a
    · rw [Set.mem_singleton_iff.1 hy]
      show f (u l) ∈ Ainf' l
      rw [map_u]
      exact u_mem) hx

theorem pow_u (y : B l) (n : ℕ) : y * (l : B l) ^ n * u l ^ n = y := by
  rw [mul_assoc, ← mul_pow, mul_comm (l : B l), u_mul, one_pow, mul_one]

def rep (l : ℕ) [Fact l.Prime] : Subring (B l) where
  carrier := {x | ∃ (a : AInf ℂ_[l] l) (k : ℕ), x = aB l a * u l ^ k}
  mul_mem' := by
    rintro _ _ ⟨a, k, rfl⟩ ⟨b, j, rfl⟩
    exact ⟨a * b, k + j, by rw [map_mul, pow_add]; ring⟩
  one_mem' := ⟨1, 0, by rw [map_one, pow_zero, mul_one]⟩
  add_mem' := by
    rintro _ _ ⟨a, k, rfl⟩ ⟨b, j, rfl⟩
    refine ⟨a * (l : AInf ℂ_[l] l) ^ j + b * (l : AInf ℂ_[l] l) ^ k, k + j, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast]
    calc aB l a * u l ^ k + aB l b * u l ^ j =
        aB l a * (l : B l) ^ j * u l ^ j * u l ^ k + aB l b * (l : B l) ^ k * u l ^ k * u l ^ j := by
          rw [pow_u, pow_u]
      _ = _ := by ring
  zero_mem' := ⟨0, 0, by rw [map_zero, zero_mul]⟩
  neg_mem' := by
    rintro _ ⟨a, k, rfl⟩
    exact ⟨-a, k, by rw [map_neg, neg_mul]⟩

theorem mem_rep {x : B l} (hx : x ∈ Ainf' l) : ∃ (a : AInf ℂ_[l] l) (k : ℕ), x = aB l a * u l ^ k :=
  (Subring.closure_le (t := rep l)).2 (by
    rintro y (⟨a, rfl⟩ | hy)
    · exact ⟨a, 0, by rw [pow_zero, mul_one]⟩
    · rw [Set.mem_singleton_iff.1 hy]
      exact ⟨1, 1, by rw [map_one, one_mul, pow_one]⟩) hx

end BaseC

end period_ring_base
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.ABInjective =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.CoeffLMul =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.CoeffLMul", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.ABInjective\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.DiscreteValuationRing\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

namespace BaseC

variable {l : ℕ} [Fact l.Prime]

theorem ainf_φ : ∀ x ∈ Ainf' l, φ l x ∈ Ainf' l :=
  map_mem fun a => by rw [φ_aB]; exact aB_mem _

theorem ainf_σ (g : GQ l) : ∀ x ∈ Ainf' l, σB g x ∈ Ainf' l :=
  map_mem fun a => by
    obtain ⟨a', h⟩ := σ_aB g a
    rw [h]; exact aB_mem _

theorem ι_u : ι l (u l) = qQ l ((l : ℚ_[l])⁻¹) := by
  refine inv_uniq (c := (l : BdR l)) ?_ ?_
  · rw [← map_natCast (ι l) l, ← map_mul, u_mul, map_one]
  · rw [← map_natCast (qQ l) l, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), map_one]

theorem ainf_plus : ∀ x ∈ Ainf' l, ι l x ∈ Plus l := fun x hx =>
  (Subring.closure_le (t := (Plus l).comap (ι l))).2 (by
    rintro y (⟨a, rfl⟩ | hy)
    · refine ⟨ACris.iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) a), ?_⟩
      exact (Loc2.lift_mk₀ (iC l) (isUnit_iC_l l) (isUnit_image_period l) _).symm
    · rw [Set.mem_singleton_iff.1 hy]
      show ι l (u l) ∈ Plus l
      rw [ι_u]
      exact ⟨algebraMap ℚ_[l] (BdRp l) _, rfl⟩) hx

theorem φpow_aB (h : ℕ) (a : AInf ℂ_[l] l) :
    (φ l ^ h) (aB l a) = aB l ((WittVector.frobenius : AInf ℂ_[l] l →+* AInf ℂ_[l] l)^[h] a) := by
  induction h with
  | zero => rfl
  | succ n ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, φ_aB,
      Function.iterate_succ_apply']

theorem cancel_l {N : ℕ} {y z : B l} (h : (l : B l) ^ N * y = (l : B l) ^ N * z) : y = z := by
  rw [← pow_u y N, ← pow_u z N, mul_comm y, mul_comm z, h]

theorem coeff_ne (b : AInf ℂ_[l] l) (hb : b.coeff 0 ≠ 0) (h : ℕ) :
    ((WittVector.frobenius : AInf ℂ_[l] l →+* AInf ℂ_[l] l)^[h] b).coeff 0 ≠ 0 := by
  rw [WittVector.iterate_frobenius_coeff]
  intro h0
  apply hb
  have hinj : Function.Injective (⇑(frobenius (PreTilt ↥(normInteger ℂ_[l]) l) l))^[h] :=
    Function.Injective.iterate (PerfectRing.bijective_frobenius (R := PreTilt ↥(normInteger ℂ_[l]) l)
      (p := l)).1 h
  apply hinj
  rw [iterate_frobenius, iterate_frobenius, h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]

theorem coeff_l_mul {n : ℕ} (hn : n ≠ 0) (b : AInf ℂ_[l] l) : ((l : AInf ℂ_[l] l) ^ n * b).coeff 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [show (l : AInf ℂ_[l] l) ^ (k + 1) * b = ((l : AInf ℂ_[l] l) ^ k * b) * (l : AInf ℂ_[l] l) by ring]
  exact WittVector.mul_charP_coeff_zero _

theorem ainf_eig (h : ℕ) (m : ℤ) (hm : m ≠ 0) (x : B l) (hx : x ∈ Ainf' l) (he : Eig h m x) : x = 0 := by
  obtain ⟨a, k, rfl⟩ := mem_rep hx
  have hu : (φ l ^ h) (u l) = u l := map_u _
  set F := (WittVector.frobenius : AInf ℂ_[l] l →+* AInf ℂ_[l] l)^[h] with hF
  have he' : aB l (F a) * u l ^ k = (qB l ((l : ℚ_[l]) ^ m) * aB l a) * u l ^ k := by
    have := he
    rw [Eig, map_mul, map_pow, hu, φpow_aB] at this
    rw [this]; ring
  have e : aB l (F a) = qB l ((l : ℚ_[l]) ^ m) * aB l a := by
    have k1 : ∀ y : B l, y * u l ^ k * (l : B l) ^ k = y := fun y => by
      rw [mul_right_comm]; exact pow_u y k
    rw [← k1 (aB l (F a)), he', k1]
  have hFl : F (l : AInf ℂ_[l] l) = l := Function.iterate_fixed (map_natCast _ l) h
  have hFmul : ∀ (N : ℕ) (b : AInf ℂ_[l] l), F ((l : AInf ℂ_[l] l) ^ N * b) = (l : AInf ℂ_[l] l) ^ N * F b :=
    fun N b => by
      rw [hF, iterate_map_mul, iterate_map_pow, ← hF, hFl]
  have haB : ∀ (N : ℕ) (b : AInf ℂ_[l] l), aB l ((l : AInf ℂ_[l] l) ^ N * b) = (l : B l) ^ N * aB l b :=
    fun N b => by rw [map_mul, map_pow, map_natCast]
  suffices ha : a = 0 by rw [ha, map_zero, zero_mul]
  by_contra ha
  obtain ⟨N, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a ha
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : n ≠ 0 := by rintro rfl; exact hm rfl
    have e1 : (l : B l) ^ N * aB l (F b) = (l : B l) ^ N * aB l ((l : AInf ℂ_[l] l) ^ n * b) :=
      calc (l : B l) ^ N * aB l (F b) = aB l (F ((l : AInf ℂ_[l] l) ^ N * b)) := by rw [hFmul, haB]
        _ = qB l ((l : ℚ_[l]) ^ (n : ℤ)) * aB l ((l : AInf ℂ_[l] l) ^ N * b) := e
        _ = _ := by rw [zpow_natCast, map_pow, map_natCast, haB, haB]; ring
    have e2 := aB_injective (cancel_l e1)
    have c := congrArg (fun w => WittVector.coeff w 0) e2
    rw [coeff_l_mul hn] at c
    exact coeff_ne b hb h c
  · have hn : n ≠ 0 := by rintro rfl; exact hm (by simp)
    have hq : qB l ((l : ℚ_[l]) ^ (-(n : ℤ))) * (l : B l) ^ n = 1 := by
      rw [← map_natCast (qB l) l, ← map_pow, ← map_mul, _root_.zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)), map_one]
    have e1 : (l : B l) ^ N * aB l (F b * (l : AInf ℂ_[l] l) ^ n) = (l : B l) ^ N * aB l b :=
      calc (l : B l) ^ N * aB l (F b * (l : AInf ℂ_[l] l) ^ n)
          = aB l (F ((l : AInf ℂ_[l] l) ^ N * b)) * (l : B l) ^ n := by
            rw [hFmul, map_mul, haB, map_pow, map_natCast]; ring
        _ = qB l ((l : ℚ_[l]) ^ (-(n : ℤ))) * aB l ((l : AInf ℂ_[l] l) ^ N * b) * (l : B l) ^ n := by
            rw [e]
        _ = _ := by rw [mul_right_comm, hq, one_mul, haB]
    have e2 := aB_injective (cancel_l e1)
    have c := congrArg (fun w => WittVector.coeff w 0) e2
    rw [mul_comm, coeff_l_mul hn] at c
    exact hb c.symm

end BaseC

end period_ring_base
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.CoeffLMul =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.BaseAinfPlus =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.BaseAinfPlus", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.CoeffLMul\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace period_ring_base

open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

theorem base_ainf_φ (l : ℕ) [Fact l.Prime] : ∀ x ∈ Ainf' l, φ l x ∈ Ainf' l :=
  BaseC.ainf_φ

theorem base_ainf_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l), ∀ x ∈ Ainf' l, σB g x ∈ Ainf' l :=
  BaseC.ainf_σ

theorem base_ainf_plus (l : ℕ) [Fact l.Prime] : ∀ x ∈ Ainf' l, ι l x ∈ Plus l :=
  BaseC.ainf_plus

theorem base_ainf_eig (l : ℕ) [Fact l.Prime] :
    ∀ (h : ℕ) (m : ℤ), m ≠ 0 → ∀ x ∈ Ainf' l, Eig h m x → x = 0 :=
  fun h m hm x hx he => BaseC.ainf_eig h m hm x hx he

end period_ring_base
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.BaseAinfPlus =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification\npublic import GroundTheory.PAdicHodge.BCrisEigen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace period_ring_base

open Formalism.Per6
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

open Topology Filter

namespace BaseB

variable {l : ℕ} [Fact l.Prime]

theorem toBot_one : toBot (1 : GQ l) = 1 := AlgEquiv.ext fun _ => rfl

theorem toBot_mul (g h : GQ l) : toBot (g * h) = toBot g * toBot h := AlgEquiv.ext fun _ => rfl

theorem th_alg (b : BdRp l) : th l (algebraMap (BdRp l) (BdR l) b) = θD l b := by
  have hm : algebraMap (BdRp l) (BdR l) b ∈ Plus l := ⟨b, rfl⟩
  rw [th, dite_eq_left hm]
  congr 1
  exact IsFractionRing.injective (BdRp l) (BdR l) (RingHom.mem_range.1 hm).choose_spec

theorem σD_alg (g : GQ l) (b : BdRp l) :
    σD g (algebraMap (BdRp l) (BdR l) b) = algebraMap (BdRp l) (BdR l) (toBot g • b) :=
  galBdRField_algebraMap _ _

alias tQ_alg := _root_.DeRhamTwist.Twist.tQ_eq

theorem orbit_alg (y : PadicAlgCl l) : Continuous fun g : GQ l => g y := by
  refine continuous_iff_continuousAt.2 fun g₀ => tendsto_nhds_of_eventually_eq ?_
  let S := MulAction.stabilizer (GQ l) y
  have hS : (S : Set (GQ l)) ∈ 𝓝 (g₀⁻¹ * g₀) := by
    rw [inv_mul_cancel]
    exact (stabilizer_isOpen_of_isIntegral y).mem_nhds S.one_mem
  filter_upwards [(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hS] with g hg
  have h : (g₀⁻¹ * g) • y = y := hg
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h

theorem σC_coe (g : GQ l) (y : PadicAlgCl l) : σC g (y : ℂ_[l]) = ((g y : PadicAlgCl l) : ℂ_[l]) := by
  show toBot g • (y : ℂ_[l]) = _
  rw [gal_smul_coe]
  rfl

theorem σC_dist (g : GQ l) (x y : ℂ_[l]) : dist (σC g x) (σC g y) = dist x y :=
  (isometry_smul_gal (toBot g)).dist_eq x y

end BaseB

open BaseB

variable (l : ℕ) [Fact l.Prime]

theorem base_σD_one : ∀ x, σD (1 : GQ l) x = x := by
  intro x
  show galBdRField (toBot 1) x = x
  rw [toBot_one, galBdRField_one]
  rfl

theorem base_σD_mul : ∀ (g h : GQ l) x, σD (g * h) x = σD g (σD h x) := by
  intro g h x
  show galBdRField (toBot (g * h)) x = galBdRField (toBot g) (galBdRField (toBot h) x)
  rw [toBot_mul, galBdRField_mul]
  rfl

theorem base_σC_one : ∀ x, σC (1 : GQ l) x = x := by
  intro x
  show galCp (toBot 1) x = x
  rw [toBot_one, galCp_one]
  rfl

theorem base_σC_mul : ∀ (g h : GQ l) x, σC (g * h) x = σC g (σC h x) := by
  intro g h x
  show galCp (toBot (g * h)) x = galCp (toBot g) (galCp (toBot h) x)
  rw [toBot_mul, galCp_mul]
  rfl

theorem base_σ_u : ∀ g : GQ l, σD g (uQ l) = uQ l + qQ l (κ g) * tQ l := by
  intro g
  show σD g (algebraMap (BdRp l) (BdR l) (uBdR l)) = _
  rw [σD_alg, gal_smul_uBdR_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g), map_add (f := _),
    map_mul, tQ_alg]
  rfl

theorem base_κ_mul : ∀ g h : GQ l, κ (g * h) = κ g + χ g * κ h := by
  intro g h
  simp only [κ, χ]
  rw [toBot_mul, kummerC_mul, DeRhamTwist.Twist.cycloChar_toBot]
  push_cast
  ring

theorem base_plus_σ : ∀ (g : GQ l) x, x ∈ Plus l → σD g x ∈ Plus l := by
  rintro g _ ⟨b, rfl⟩
  exact ⟨toBot g • b, (σD_alg g b).symm⟩

theorem base_th_σ : ∀ (g : GQ l) x, x ∈ Plus l → th l (σD g x) = σC g (th l x) := by
  rintro g _ ⟨b, rfl⟩
  rw [σD_alg, th_alg, th_alg]
  exact thetaBDeRhamPlusField_gal_smul _ _

theorem base_th_add : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x + y) = th l x + th l y := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_add (f := _), th_alg, th_alg, th_alg, map_add (f := _)]

theorem base_th_mul : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x * y) = th l x * th l y := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, th_alg, th_alg, th_alg, map_mul]

theorem base_th_q : ∀ q, qQ l q ∈ Plus l ∧ th l (qQ l q) = algebraMap ℚ_[l] ℂ_[l] q := by
  intro q
  refine ⟨⟨_, rfl⟩, ?_⟩
  show th l (algebraMap (BdRp l) (BdR l) (algebraMap ℚ_[l] (BdRp l) q)) = _
  rw [th_alg]
  exact thetaBDeRhamPlusField_algebraMap l q

theorem base_t_plus : tQ l ∈ Plus l := ⟨ACris.iota ℂ_[l] l (tA l), rfl⟩

theorem base_th_zero : ∀ x ∈ Plus l, (th l x = 0 ↔ ∃ y ∈ Plus l, x = tQ l * y) := by
  rintro _ ⟨b, rfl⟩
  rw [th_alg]
  have hk : θD l b = 0 ↔ b ∈ IsLocalRing.maximalIdeal (BdRp l) := by
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker]
    rfl
  rw [hk, maximalIdeal_eq_span_tBdR, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨_, ⟨c, rfl⟩, by rw [← hc, tQ_alg, ← map_mul, mul_comm]⟩
  · rintro ⟨_, ⟨c, rfl⟩, h⟩
    refine ⟨c, IsFractionRing.injective (BdRp l) (BdR l) ?_⟩
    rw [h, tQ_alg, ← map_mul, mul_comm]

theorem base_val : ∀ x : BdR l, x ≠ 0 → ∃ (i : ℤ) (u v : BdR l), u ∈ Plus l ∧ v ∈ Plus l ∧ u * v = 1 ∧
    x = tQ l ^ i * u := by
  intro x hx
  obtain ⟨i, u, h⟩ := ACris.exists_eq_zpow_mul_unit untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one hx
  refine ⟨i, algebraMap (BdRp l) (BdR l) (u : BdRp l), algebraMap (BdRp l) (BdR l) ((u⁻¹ : (BdRp l)ˣ) : BdRp l),
    ⟨_, rfl⟩, ⟨_, rfl⟩, by rw [← map_mul, Units.mul_inv, map_one], ?_⟩
  rw [h, tQ_alg]
  rfl

theorem base_orbit : ∀ x : ℂ_[l], Continuous fun g : GQ l => σC g x := by
  intro x
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨_, ⟨y, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 (UniformSpace.Completion.denseRange_coe x) (ε / 3)
    (by positivity)
  have hc := (UniformSpace.Completion.continuous_coe (PadicAlgCl l)).comp (orbit_alg (l := l) y)
  filter_upwards [Metric.tendsto_nhds.1 (hc.tendsto g₀) (ε / 3) (by positivity)] with g hg
  have h1 : dist (((g y : PadicAlgCl l) : ℂ_[l])) (((g₀ y : PadicAlgCl l) : ℂ_[l])) < ε / 3 := hg
  calc dist (σC g x) (σC g₀ x)
      ≤ dist (σC g x) (σC g (y : ℂ_[l])) + dist (σC g (y : ℂ_[l])) (σC g₀ (y : ℂ_[l])) +
          dist (σC g₀ (y : ℂ_[l])) (σC g₀ x) := dist_triangle4 _ _ _ _
    _ < ε := by
      rw [σC_dist, σC_dist, σC_coe, σC_coe, dist_comm (y : ℂ_[l]) x]
      linarith

end period_ring_base
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.ThetaAlgebraMap.ThAlgebraMap =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.ThetaAlgebraMap.ThAlgebraMap", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

namespace EstT

variable {l : ℕ} [Fact l.Prime]

theorem qB_mem_ainf (q : ℚ_[l]) : qB l q ∈ Ainf' l := by
  have key : ∀ z : ℤ_[l], qB l (algebraMap ℤ_[l] ℚ_[l] z) ∈ Ainf' l := fun z => by
    have e : qB l (algebraMap ℤ_[l] ℚ_[l] z) = zB l z := IsLocalization.lift_eq _ _
    rw [e]
    exact Subring.subset_closure (Or.inl ⟨ainfMap l (zA l z), rfl⟩)
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors ℤ_[l]) q
  have hs : (s : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsu := PadicInt.unitCoeff_spec hs
  set u := PadicInt.unitCoeff hs
  set n := (s : ℤ_[l]).valuation
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have e : IsLocalization.mk' ℚ_[l] z s =
      algebraMap ℤ_[l] ℚ_[l] (z * ↑u⁻¹) * ((l : ℚ_[l])⁻¹) ^ n := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, hsu]
    simp only [map_mul, map_pow, map_natCast]
    have hx : ((l : ℚ_[l])⁻¹) ^ n * (l : ℚ_[l]) ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hl0, one_pow]
    have hu : algebraMap ℤ_[l] ℚ_[l] (↑u⁻¹ : ℤ_[l]) * algebraMap ℤ_[l] ℚ_[l] (u : ℤ_[l]) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap ℤ_[l] ℚ_[l] z) * ((l : ℚ_[l])⁻¹) ^ n * (l : ℚ_[l]) ^ n) * hu -
      algebraMap ℤ_[l] ℚ_[l] z * hx
  show qB l (IsLocalization.mk' ℚ_[l] z s) ∈ _
  rw [e, map_mul, map_pow]
  exact (Ainf' l).mul_mem (key _) ((Ainf' l).pow_mem (Subring.subset_closure (Or.inr rfl)) _)

end EstT

end period_ring_base
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.ThetaAlgebraMap.ThAlgebraMap =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.BaseFixed =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.BaseFixed", "h": "module\n\npublic import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification\npublic import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InvRestrictScalarsMem\npublic import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.ThetaAlgebraMap.ThAlgebraMap\nimport GroundTheory.PAdicHodge.ACrisFrobFixed\nimport GroundTheory.PAdicHodge.BCrisPlusInvariants\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

namespace BaseA

variable {l : ℕ} [Fact l.Prime]

open GroundTheory.PAdicHodge.ACris in
theorem uB_root {ζ : PadicAlgCl l} {m : ℕ} (hm : 0 < m) (hc : m.Coprime l) (hζ : ζ ^ m = 1)
    (h : ζ ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) : PositivityTheory.LocInh.uB l ⟨ζ, h⟩ ∈ Ainf' l := by
  obtain ⟨T, hT, hθT⟩ := exists_teichmuller_rootOfUnity hm hc hζ
  have hζ0 : (ζ : ℂ_[l]) ≠ 0 := by
    intro h0
    have := norm_eq_one_of_pow_eq_one hm (show (ζ : ℂ_[l]) ^ m = 1 by
      rw [PadicComplex.coe_eq, ← map_pow, hζ, map_one])
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hx : iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) T) = algClToBdR l ζ := by
    apply eq_of_pow_eq_one_of_theta_eq hm
    · rw [← map_pow, ← map_pow, hT, map_one, map_one]
    · rw [← map_pow, hζ, map_one]
    · rw [thetaAlgHom_apply, thetaField_iota, theta_algebraMap, hθT, thetaAlgHom_algClToBdR]
    · rw [thetaAlgHom_algClToBdR]; exact hζ0
  have e : aB l T = PositivityTheory.LocInh.uB l ⟨ζ, h⟩ := by
    apply base_ι_inj l
    have e1 : ι l (aB l T) = algebraMap (BdRp l) (BdR l)
        (iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) T)) := ι_cB l _
    rw [e1, hx, ι_eq, PositivityTheory.LocInh.ιCD_uB, PositivityTheory.LocInh.GaloisCommutant.oD_apply]
  rw [← e]
  exact Subring.subset_closure (Or.inl ⟨T, rfl⟩)

theorem uB_mem (c : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) : PositivityTheory.LocInh.uB l c ∈ Ainf' l := by
  obtain ⟨c, hc⟩ := c
  have e : (Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l).toSubalgebra =
      Algebra.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1} :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  have adj : ∀ x, x ∈ Algebra.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1} →
      x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l := fun x hx => by
    have : x ∈ (Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l).toSubalgebra := e ▸ hx
    exact this
  have key : ∀ x ∈ Algebra.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1},
      ∀ h : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l, PositivityTheory.LocInh.uB l ⟨x, h⟩ ∈ Ainf' l := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      intro h
      obtain ⟨m, hm, hl, hxm⟩ := hx
      exact uB_root hm (Nat.Coprime.symm (((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl)) hxm h
    | algebraMap r =>
      intro h
      have : (⟨algebraMap ℚ_[l] (PadicAlgCl l) r, h⟩ : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) =
          algebraMap ℚ_[l] ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) r := rfl
      rw [this, PositivityTheory.LocInh.uB_algebraMap, ← qB_eq]
      exact EstT.qB_mem_ainf r
    | add x y hx hy ihx ihy =>
      intro h
      have : (⟨x + y, h⟩ : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) = ⟨x, adj x hx⟩ + ⟨y, adj y hy⟩ := rfl
      rw [this, map_add (f := _)]
      exact Subring.add_mem _ (ihx (adj x hx)) (ihy (adj y hy))
    | mul x y hx hy ihx ihy =>
      intro h
      have : (⟨x * y, h⟩ : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) = ⟨x, adj x hx⟩ * ⟨y, adj y hy⟩ := rfl
      rw [this, map_mul]
      exact Subring.mul_mem _ (ihx (adj x hx)) (ihy (adj y hy))
  exact key c (by have : c ∈ (Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l).toSubalgebra := hc; rwa [e] at this) hc

end BaseA

open BaseA

theorem base_fixed' (l : ℕ) [Fact l.Prime] : ∀ L : Fld l, FiniteDimensional ℚ_[l] L →
    ∃ (f : ℕ) (b : Fin f → B l),
    (∀ i, b i ∈ Ainf' l ∧ ∀ σ ∈ L.fixingSubgroup, σB σ (b i) = b i) ∧
    ∀ x, (∀ σ ∈ L.fixingSubgroup, σB σ x = x) → ∃ q : Fin f → ℚ_[l], x = ∑ i, qB l (q i) * b i := by
  intro L hL
  let L0 : IntermediateField ℚ_[l] (PadicAlgCl l) := L ⊓ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l
  have : FiniteDimensional ℚ_[l] L0 := by
    have : FiniteDimensional ℚ_[l] L.toSubalgebra.toSubmodule := hL
    exact Submodule.finiteDimensional_of_le (S₂ := L.toSubalgebra.toSubmodule)
      (S₁ := L0.toSubalgebra.toSubmodule) fun x hx => (IntermediateField.mem_inf.1 hx).1
  let bas := Module.finBasis ℚ_[l] L0
  let c : Fin (Module.finrank ℚ_[l] L0) → ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) :=
    fun i => ⟨(bas i : PadicAlgCl l), (IntermediateField.mem_inf.1 (bas i).2).2⟩
  refine ⟨_, fun i => PositivityTheory.LocInh.uB l (c i), fun i => ⟨uB_mem _, fun σ hσ => ?_⟩, fun x hx => ?_⟩
  · apply base_ι_inj l
    rw [base_ι_σ, ι_eq, PositivityTheory.LocInh.ιCD_uB, PositivityTheory.LocInh.σD_oD]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (IntermediateField.mem_inf.1 (bas i).2).1
  · obtain ⟨k, hkL, hk⟩ := PositivityTheory.LocInh.invB ⟨L, hL⟩ x fun g hg => hx g hg
    let k0 : L0 := ⟨k, IntermediateField.mem_inf.2 ⟨hkL, k.2⟩⟩
    refine ⟨fun i => bas.repr k0 i, ?_⟩
    rw [← hk]
    have hsum := congrArg (fun y : L0 => (y : PadicAlgCl l)) (bas.sum_repr k0).symm
    have hk' : k = ∑ i, algebraMap ℚ_[l] ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) (bas.repr k0 i) * c i := by
      apply Subtype.ext
      refine hsum.trans ?_
      simp only [IntermediateField.coe_sum, Algebra.smul_def, IntermediateField.coe_mul, c]
      rfl

    rw [hk', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, PositivityTheory.LocInh.uB_algebraMap, qB_eq]

end period_ring_base
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.BaseFixed =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.Base =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.Base", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.BasedP\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.BaseAinfPlus\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero\npublic import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.BaseFixed\nimport Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace period_ring_base

theorem base : PeriodRingBase := fun l _ =>
  { dom := base_dom l
    ι_inj := base_ι_inj l
    σ_one := base_σ_one l
    σ_mul := base_σ_mul l
    σD_one := base_σD_one l
    σD_mul := base_σD_mul l
    σC_one := base_σC_one l
    σC_mul := base_σC_mul l
    φ_σ := base_φ_σ l
    ι_σ := base_ι_σ l
    φ_q := base_φ_q l
    σ_q := base_σ_q l
    ι_q := base_ι_q l
    ι_t := period_image_eq l
    t_unit := base_t_unit l
    frobenius_period := frobenius_period_holds l
    galois_t_transform := galois_period_cyclotomic l
    σ_u := base_σ_u l
    κ_mul := base_κ_mul l
    κ_cont := _root_.period_ring_base.continuous_κ l
    χ_cont := base_χ_cont l
    ι_Bst := base_ι_Bst l
    u_Bst := base_u_Bst l
    plus_σ := base_plus_σ l
    th_σ := base_th_σ l
    th_add := base_th_add l
    th_mul := base_th_mul l
    th_q := base_th_q l
    th_zero := base_th_zero l
    t_plus := base_t_plus l
    val := base_val l
    orbit := base_orbit l
    fs_ker := base_fs_ker l
    fs_surj := base_fs_surj l
    ainf_φ := base_ainf_φ l
    ainf_σ := base_ainf_σ l
    ainf_plus := base_ainf_plus l
    ainf_eig := base_ainf_eig l
    fixed := base_fixed' l
    no_kummer := base_no_kummer l }

end period_ring_base
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.Base =====
