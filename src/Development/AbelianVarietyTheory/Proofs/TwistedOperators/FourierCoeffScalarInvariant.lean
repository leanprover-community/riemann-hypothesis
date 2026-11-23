module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


namespace GlobalTheory.MovedKappaArith

theorem selfDualIntertwiner_baseVector_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {e0 : VC D N N' → ℂ} (he : oddE0 D cc δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') e0 ≠ 0 := by
  have s0 := GlobalTheory.MovedVacuum.sd_stdL D N
  have s0' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, s0, s0', rfl⟩
  have k1 : KLat D (tor0 D cc δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1
  intro h
  exact GlobalTheory.TrueTheta.ne_zero_of_like hC ht s0 s0' he.2.2.2.1
    (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])

theorem applyAt0_monomial (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

end GlobalTheory.MovedKappaArith
