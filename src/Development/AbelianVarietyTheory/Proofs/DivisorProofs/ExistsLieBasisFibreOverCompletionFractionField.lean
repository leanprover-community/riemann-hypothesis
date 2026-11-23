module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

noncomputable section

open Limits

namespace GlobalTheory.LieLatGen

theorem exists_isLieBasis_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)), ∃ v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G), IsLieBasis v' ∧ ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ := by
  intro E _ _ _ H K _ _ B t₀ m2 F T iK t' n'
  have hF : IsGrpPullback F.P₀.A B.t.G (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  have hm : IsGrpPullback t₀.G B.t.G (spMap (algebraMap (𝓞 K) K)) m2.φ := m2.cart
  have hn : IsGrpPullback t'.G t₀.G (spMap iK) n'.φ := n'.cart
  have hc : IsGrpPullback t'.G B.t.G (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) (n'.φ ≫ m2.φ) := hn.comp hm
  have w : (n'.φ ≫ m2.φ) ≫ B.t.G.hom = (t'.G.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [hc.1.w, Category.assoc]
  have hq : IsGrpPullback t'.G F.P₀.A (spMap iK) (hF.1.lift _ _ w) :=
    IsGrpPullback.cancel hF (hc.congr rfl (hF.1.lift_fst _ _ w).symm) (hF.1.lift_snd _ _ w)
  have := F.P₀.isAb.comm
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange K T.Fr iK _ _ _ hq F.P₀.isAb.smooth _ F.v F.basis
  refine ⟨v', hb, fun k => ?_⟩
  rw [← hF.1.lift_fst _ _ w, ← Category.assoc, hv' k, Category.assoc]
  rfl

end GlobalTheory.LieLatGen
