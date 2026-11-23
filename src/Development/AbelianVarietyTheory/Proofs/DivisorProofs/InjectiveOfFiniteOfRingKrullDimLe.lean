module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteMapInj

theorem injective_of_finite_of_ringKrullDim_le (A R : Type) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] (b : A →+* R) :
    b.Finite → ringKrullDim A ≤ ringKrullDim R → Function.Injective b := by
  intro hfin hdim
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  set I := RingHom.ker b
  have hxI : x ∈ I := hx

  have hcomp : b.kerLift.comp (Ideal.Quotient.mk I) = b := by
    ext a; rfl
  have hfin' : b.kerLift.Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  letI : Algebra (A ⧸ I) R := b.kerLift.toAlgebra
  haveI : Algebra.IsIntegral (A ⧸ I) R := ⟨hfin'.to_isIntegral⟩
  have h1 : ringKrullDim R ≤ ringKrullDim (A ⧸ I) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ I) R))
      fun P Q h => Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) h
  have h2 : ringKrullDim (A ⧸ I) + 1 ≤ ringKrullDim A :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hxI)
  have h3 : ringKrullDim R + 1 ≤ ringKrullDim R :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans hdim
  have htop : ringKrullDim R + 1 < ⊤ :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans_lt
      ringKrullDim_lt_top
  have hbot : ringKrullDim R ≠ ⊥ := fun h => by
    have := ringKrullDim_nonneg_of_nontrivial (R := R)
    rw [h] at this
    exact absurd this (by simp)
  generalize ringKrullDim R = d at h3 htop hbot
  induction d with
  | bot => exact hbot rfl
  | coe e =>
    induction e with
    | top =>
      exact absurd htop (by rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]; exact lt_irrefl _)
    | coe n =>
      have : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h3
      norm_cast at this
      omega

end GlobalTheory.FiniteMapInj
