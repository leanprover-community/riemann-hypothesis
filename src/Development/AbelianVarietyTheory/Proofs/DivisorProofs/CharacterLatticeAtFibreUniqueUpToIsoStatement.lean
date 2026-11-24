module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreUniqueUpToIso
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.characterLatticeAtFibre_unique_up_to_iso : ∀ (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → IsPrimitiveRoot (ζ : o) L → IsUnit (L : o) → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (m : I → X →+ X) (c : T → X →+ ZMod L) (m' : I → X' →+ X') (c' : T → X' →+ ZMod L) (w : M.Z), LatAt f gγ ζ L m c w → LatAt f gγ ζ L m' c' w → ∃ e : X ≃+ X', (∀ i x, e (m i x) = m' i (e x)) ∧ ∀ t x, c' t (e x) = c t x := by
  first | exact @GlobalTheory.UPoinc.GFibUniq.latAt_unique | exact GlobalTheory.UPoinc.GFibUniq.latAt_unique | (intros; apply GlobalTheory.UPoinc.GFibUniq.latAt_unique <;> assumption)
