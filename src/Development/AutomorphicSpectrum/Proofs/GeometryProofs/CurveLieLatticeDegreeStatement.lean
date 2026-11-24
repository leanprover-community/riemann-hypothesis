module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieLatticeDegree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.curve_lie_lattice_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub | exact GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub | (intros; apply GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub <;> assumption)
