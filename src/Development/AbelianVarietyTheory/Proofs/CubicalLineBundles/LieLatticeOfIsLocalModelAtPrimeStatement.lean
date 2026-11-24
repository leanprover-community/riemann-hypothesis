module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrime
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


theorem _root_.GlobalTheory.T.lieLattice_of_isLocalModel_at_prime : HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth) (𝔭 : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), KeyPow.IsLocalModel (F.key hg rig hr th hth) 𝔭 a M → (∀ i, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  first | exact @GlobalTheory.CM.lieLat_of_isLocalModel | exact GlobalTheory.CM.lieLat_of_isLocalModel | (intros; apply GlobalTheory.CM.lieLat_of_isLocalModel <;> assumption)
