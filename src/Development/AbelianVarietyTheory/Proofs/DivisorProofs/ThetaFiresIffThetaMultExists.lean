module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ThetaKernelFiring
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaMultiplicity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPrimeMultOfFiresAt
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.ThetaFiresOfMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem exists_isThetaMult_of_firesAt {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
    (h : ∀ x, FiresAt R i t x) : ∃ y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)), IsThetaMult R i t y :=
  GlobalTheory.ThetaFiresLinear.exists_linear_lift (lowT (R.MW i (sg0 D A))) (R.Wall i (sg0 D A)) (R.νV i t) (R.fdV i t)
    (kernel R i t) (R.ptP i t) (GlobalTheory.ThetaFiresLinear.kernelL R i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t))
    (fun _ _ _ => rfl) (fun _ => rfl) (R.ioP i) (R.extV i t) h

end GlobalTheory.ThetaFiresOfMult

end
