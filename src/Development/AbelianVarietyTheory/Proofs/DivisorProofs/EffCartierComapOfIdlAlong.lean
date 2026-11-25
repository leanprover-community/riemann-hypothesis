module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdlAlongEqIdealAlong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.NormBlLift

theorem effCartier_comap_of_idlAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (a : Sp R ⟶ X) (f : R) (hf : f ≠ 0) (hJ : idlAlong J a = Ideal.span {f}) :
    FinalTheorems.EffCartier (J.comap a) := by
  rw [idlAlong_eq_idealAlong, GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone.idealAlong] at hJ
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv with he
  have hI : (J.comap a).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {e.symm f} := by
    have h2 := congrArg (Ideal.map e.symm.toRingHom) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_map] at h2
    have : e.symm.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = RingHom.id _ := by
      ext x; exact e.symm_apply_apply x
    rw [this, Ideal.map_id] at h2
    exact h2
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, e.symm f, trivial, ?_, hI⟩
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_left hf
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_right hf

end GlobalTheory.NormBlLift
