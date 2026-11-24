module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChange
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.degree_lieLattices_cmTriple_baseChange : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (T : PAT H (Sp (𝓞 K))) (T' : PAT H (Sp (𝓞 K'))) (_ : SABMap T'.t T.t (spMap (RingOfIntegers.mapRingHom j))) (F : GenFib T.pol) (F' : GenFib T'.pol) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K' (Fin F'.P₀.g → K')), F.IsHerm h → F'.IsHerm h' → deg h' F'.lieLat = deg h F.lieLat ∧ ∀ τ : 𝓞 E →+* 𝓞 K, deg h' (F'.eigLat T'.t.act ((RingOfIntegers.mapRingHom j).comp τ)) = deg h (F.eigLat T.t.act τ) := by
  first | exact @GlobalTheory.CM.LieBaseChange.deg_lieLat_eigLat_baseChange | exact GlobalTheory.CM.LieBaseChange.deg_lieLat_eigLat_baseChange | (intros; apply GlobalTheory.CM.LieBaseChange.deg_lieLat_eigLat_baseChange <;> assumption)
