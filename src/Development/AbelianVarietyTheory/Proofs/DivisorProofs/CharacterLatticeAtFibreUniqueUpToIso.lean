module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtIffOfSpecializes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Parity
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

noncomputable section

namespace GlobalTheory.UPoinc.GFibUniq

theorem isPrimitiveRoot_map {o : Type} [CommRing o] [IsDomain o] {ζ : o} {L : ℕ} (hL : 0 < L)
    (hζ : IsPrimitiveRoot ζ L) (hu : IsUnit (L : o)) (κ : Type) [Field κ] (a : o →+* κ) : IsPrimitiveRoot (a ζ) L := by
  haveI : NeZero (L : κ) := ⟨by simpa using (hu.map a).ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have hr := (hζ.isRoot_cyclotomic hL).map (f := a)
  simpa [Polynomial.map_cyclotomic] using hr

theorem latAt_unique : ∀ (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → IsPrimitiveRoot (ζ : o) L → IsUnit (L : o) → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (m : I → X →+ X) (c : T → X →+ ZMod L) (m' : I → X' →+ X') (c' : T → X' →+ ZMod L) (w : M.Z), LatAt f gγ ζ L m c w → LatAt f gγ ζ L m' c' w → ∃ e : X ≃+ X', (∀ i x, e (m i x) = m' i (e x)) ∧ ∀ t x, c' t (e x) = c t x := by
  intro o Ω _ _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hu X X' _ _ _ _ _ _ m c m' c' w h h'
  haveI : IsSeparated G.hom := hG.separated
  exact LatAt.unique hL (fun κ _ a => isPrimitiveRoot_map hL hζ hu κ a) h h'

end GlobalTheory.UPoinc.GFibUniq
