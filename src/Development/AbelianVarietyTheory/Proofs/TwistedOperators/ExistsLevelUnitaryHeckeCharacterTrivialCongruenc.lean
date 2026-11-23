module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.HeckeLevel

theorem add_mul_sub_one {R : Type} [CommRing R] (m c : ℕ) (w : R) :
    1 + ((m * c : ℕ) : R) * w - 1 = m • ((c : R) * w) := by
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem exists_level : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ∣ N → ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1 := by
  intro D ν hν
  obtain ⟨N₀, hN₀, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν.1
  refine ⟨N₀, hN₀, ?_⟩
  rintro N ⟨c, rfl⟩ u hu ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  have key : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z : Lev.EAf D) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E → z ∈ intAE D :=
    fun z hz => (GlobalTheory.IdemSupport.mem_intAE_iff z).2 hz
  have hint : ∀ (a : AE D) (v : Lev.EAf D), v ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
      toEAf D a = 1 + ((N₀ * c : ℕ) : Lev.EAf D) * v → finPart D a ∈ intAE D := by
    intro a v hv ha
    refine key _ ?_
    change toEAf D a ∈ _
    rw [ha]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) hv)
  refine hker u ⟨hu, hint _ w hw e, hint _ w' hw' e'⟩
    ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm ((c : Lev.EAf D) * w), key _ ?_, ?_⟩
  · rw [AlgEquiv.apply_symm_apply]
    exact mul_mem (natCast_mem _ _) hw
  · apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    rw [map_sub, map_one, map_nsmul, AlgEquiv.apply_symm_apply]
    have e2 : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (u : AE D)) : Lev.EAf D) =
      1 + ((N₀ * c : ℕ) : Lev.EAf D) * w := e
    rw [e2]
    exact add_mul_sub_one N₀ c w

end GlobalTheory.HeckeLevel
