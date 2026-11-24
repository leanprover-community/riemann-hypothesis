module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisFibreOverCompletionFractionField
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_lieBasis_fibre_over_completion_fraction_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)), ∃ v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G), IsLieBasis v' ∧ ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ := by
  first | exact @GlobalTheory.LieLatGen.exists_isLieBasis_fibre | exact GlobalTheory.LieLatGen.exists_isLieBasis_fibre | (intros; apply GlobalTheory.LieLatGen.exists_isLieBasis_fibre <;> assumption)
