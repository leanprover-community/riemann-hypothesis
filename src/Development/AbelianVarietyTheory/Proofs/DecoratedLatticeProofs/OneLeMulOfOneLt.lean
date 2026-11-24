module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumLoc

variable {D : D7}

theorem idem_mul_sum {es : Formalism.L2.DIV.Pl D.host.E → AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hes : ∀ Q ∈ S, Formalism.L2.NTheta.IsIdemAt (es Q) Q) (hc : (∑ Q ∈ S, es Q) * cA D (∑ Q ∈ S, es Q) = 0)
    {P : Formalism.L2.DIV.Pl D.host.E} (hP : P ∈ S) : es P * ∑ Q ∈ S, es Q = es P := by
  have h1 : ∀ i ∈ S, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ S, ∀ j ∈ S, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es S h1 hc
  rw [Finset.mul_sum, Finset.sum_eq_single P
    (fun Q hQ hQP => GlobalTheory.PlaceDatum.idemAt_mul (hes P hP) (hes Q hQ) (hcross P hP Q hQ) (hcross Q hQ P hP) hQP)
    (fun h => absurd hP h), h1 P hP]

end GlobalTheory.IdemSumLoc

namespace GlobalTheory.IdemSumLoc

end GlobalTheory.IdemSumLoc
