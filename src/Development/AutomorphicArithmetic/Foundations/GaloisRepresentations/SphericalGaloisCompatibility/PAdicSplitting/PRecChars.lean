module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.InfLifts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InePolLpTwOfMemIne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.recChars :
    UpperTheory.Gal.InertialTypesAlt.SuppIne → RecChars := by
  intro hSI M Ω _ _ _ _ _ A u h n T ξ hξ hsup
  haveI : CharZero (u.adicCompletion M) := charZero_of_injective_algebraMap (algebraMap M _).injective
  have hsupx : HasSupport (IrrGL.of T.ρ T.smooth T.irred).rep (chars ξ hξ) :=
    hsup.of_equiv (IrrGL.equivOf T.ρ T.smooth T.irred)
  have hnu := GlobalTheory.RoadU.TwistSupp.supp_nu_chars (u.adicCompletion M) (IrrGL.of T.ρ T.smooth T.irred) n ξ
    (fun j => ξ j * absPow _ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
    hξ (fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) (fun _ => rfl)
  refine ⟨fun hun => ⟨_, hnu.1.1 hsupx, fun y hy => ?_, hnu.2.1 hun⟩, fun rc hrc a ha t => ?_⟩
  · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · have hSI' := hSI M Ω A u h rc hrc _ _ hsupx t
    obtain ⟨a₀, ha₀, L⟩ := hrc
    obtain rfl : a₀ = a := (UpperTheory.Zero.LLC.artEx M Ω A u h).unique ha₀ ha
    have e : algNorm T = (IrrGL.of T.ρ T.smooth T.irred).nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := rfl
    have h1 : ∀ j, (rc (IrrGL.ofChar (ξ j) (hξ j))).inePol (t : G M Ω) = X - C ((ξ j (a₀ (ineIncl h t)) : ℂˣ) : ℂ) := by
      intro j
      rw [WD.inePol_of_mem_Ine _ t.2, L.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
      simp
    rw [← WD.inePol_of_mem_Ine _ t.2, e, L.nu, GlobalTheory.RoadU.DepthZeroRec.inePol_lpTw_of_mem_Ine _ _ t.2, hSI', chars,
      Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => h1 j)
