module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPrincipalTripleModelOfIsogenyDedekind
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


theorem _root_.GlobalTheory.T.exists_principalTriple_model_of_isogeny_dedekind : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : P₀.A ⟶ T₀.t.G), IsPolFibre (algebraMap R K) P P₀ φ → P.g = T₀.g → IsMonHom ψ → Surjective ψ.left → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  first | exact @GlobalTheory.CM.exists_pat_model_of_isogeny | exact GlobalTheory.CM.exists_pat_model_of_isogeny | (intros; apply GlobalTheory.CM.exists_pat_model_of_isogeny <;> assumption)
