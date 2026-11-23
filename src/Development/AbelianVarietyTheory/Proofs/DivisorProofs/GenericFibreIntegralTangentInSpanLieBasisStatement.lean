module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIntegralTangentInSpanLieBasis
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem _root_.GlobalTheory.T.genericFibre_integral_tangent_in_span_lieBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G)) (M : Fin F.P₀.g → Fin F.P₀.g → K), IsLieBasis vV → (∀ k, ∃ w : epsR K ⟶ F.P₀.A, IsLieComb (M k) F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ) → ∀ (ub : epsOver T.V T.V ⟶ G.t.G) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), IsTan ub → u'' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ ub.left → ∃ (a : Fin F.P₀.g → T.V) (w'' : epsR T.Fr ⟶ t'.G), w''.left = u'' ∧ IsLieComb (∑ k, algebraMap T.V T.Fr (a k) • fun l => iK (M k l)) v' w'' := by
  first | exact @GlobalTheory.PtDeg.LieModel.generic_coords_in_span | exact GlobalTheory.PtDeg.LieModel.generic_coords_in_span | (intros; apply GlobalTheory.PtDeg.LieModel.generic_coords_in_span <;> assumption)
