module

public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedLengthLatticeQuotientBaseChangeEq
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

@[expose] public section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

theorem _root_.GlobalTheory.T.normalizedLength_latticeQuotient_baseChange_eq : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → (l : 𝓞 K) ∈ w.asIdeal → (∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) → (a ∈ w.asIdeal ↔ ¬ IsUnit z)) → ∀ (A B : Submodule (𝓞 K) V), A.FG → B ≤ A → lenUnit (O := O) l (↥(Submodule.span O (iV '' (A : Set V))) ⧸ (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) = Formalism.L2.Col.lenUW w A B := by
  first | exact @GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | exact GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | (intros; apply GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW <;> assumption)
