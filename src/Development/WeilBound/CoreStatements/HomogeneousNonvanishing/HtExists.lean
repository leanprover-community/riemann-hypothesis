module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHens
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfChar
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfEx
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.UnitarySelfGeneration

theorem ht_char_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) :=
  PositivityTheory.HtPt.Htat.ht_char_section_of PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

theorem ht_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w :=
  PositivityTheory.HtPt.Htat.ht_exists_of PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

end PositivityTheory.UnitarySelfGeneration
