module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayPrimeOfNormIntegerCongruentOne
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.isRayPrime_of_norm_integer_congruent_one : ∀ (D : D7) (i : Fin 2) (jE : D.host.E →+* Qb), (D.host.g i).Prime → (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E) ∧ (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)}) → IsRayPrime (GlobalTheory.HeightCounting.KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g i) := by
  first | exact @GlobalTheory.RayPrimeOfNorm.isRayPrime_of_norm_eq | exact GlobalTheory.RayPrimeOfNorm.isRayPrime_of_norm_eq | (intros; apply GlobalTheory.RayPrimeOfNorm.isRayPrime_of_norm_eq <;> assumption)
