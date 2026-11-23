module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SquareSectionWeightZero

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), ∃ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) ∧ ¬ ∀ j, (f 0).f j = 0 := by
  intro R _ _ _ _ G _ _ _ D A U
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨E, hE⟩ := GlobalTheory.FamFree.exists_fam_support (F := FractionRing R) h1.globalFns h2.secTwist
    D.tau_bimult (k := 2) (by norm_num) (0 : D.toPre.X)
  have hE0 : ¬ ∀ j, (E.s 0).f j = 0 := (hE 0).2 ⟨0, by simp⟩
  obtain ⟨s, hs, -⟩ := (U.expand 2 (by norm_num)).2 E
  obtain ⟨r, hr, σ, f, -, hf, hexp⟩ := hs
  refine ⟨σ, f, hexp, fun h0 => hE0 ?_⟩
  have key := (GlobalTheory.ConstFam.secScal_iff_resF D.toPre (FractionRing R) (E.s 0) (f 0) r).1 (hf 0)
  have hf0 : (f 0 : GlobalTheory.ConstFam.SecBMod D.toPre 2 0) = 0 := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext h0
  rw [hf0] at key
  erw [map_zero] at key
  have hr' : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r ≠ 0 := by
    intro h
    apply hr
    have hinj : Function.Injective (GlobalTheory.ConstFam.toF (R := R) (FractionRing R)) :=
      (algebraMap (FractionRing R) (FractionRing R)).injective.comp (IsFractionRing.injective R _)
    exact hinj (h.trans (map_zero _).symm)
  let t : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 := E.s 0
  have k2 : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r • t = 0 := key.symm
  have e0 : t = 0 := by rw [← inv_smul_smul₀ hr' t, k2, smul_zero]
  intro j
  exact congrArg (fun q : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 => LB.Sec.f q j) e0

end GlobalTheory.SquareSectionWeightZero
