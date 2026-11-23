module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

@[expose] public section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latDetH_map_injective_isometry : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  first | exact @GlobalTheory.LoopC.DetMap.latDetH_map | exact GlobalTheory.LoopC.DetMap.latDetH_map | (intros; apply GlobalTheory.LoopC.DetMap.latDetH_map <;> assumption)
