module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDescendAlongFlatMapToLocalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sections_descend_along_flat_map_to_localDomain : ∀ (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens) (hWU : W ≤ U.1), IsCompact (W : Set X) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ρ : Γ(X, U.1) →+* R), ρ.Flat → ∀ mm : Ideal Γ(X, U.1), (maximalIdeal R).comap ρ = mm → ∀ (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W), ρ h ≠ 0 → ∀ (J : Type) [Finite J] (θ : J → Γ(X, W)), (∀ i (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s = (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) * (X.presheaf.map (homOfLE hh).op).hom (θ i) → ρ h ^ N ∣ ρ s) → ∃ g ∉ mm, ∀ i, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ i := by
  first | exact @GlobalTheory.LocRegDesc.descent | exact GlobalTheory.LocRegDesc.descent | (intros; apply GlobalTheory.LocRegDesc.descent <;> assumption)
