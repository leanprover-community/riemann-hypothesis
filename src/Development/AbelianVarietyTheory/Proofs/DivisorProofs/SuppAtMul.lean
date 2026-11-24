module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.BigOn.Exp.TupLe.Swap

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev ThAt (a : AE D) (b Φ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) a
    (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 b Φ f


open Classical in
def adjDat (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (x : WO (Vc D i) (Wc D i)) : ℂ :=
  if IsHalf a x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0


variable {R} in
open Classical in
def keepPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∈ Q'


variable {R} in
open Classical in
def flipPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∉ Q'

end Defs

theorem suppAt_mul' {D : D7} {V : HSp D} {e : AE D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) :
    SuppAt e V (a * b) := by
  intro i j
  have hm : mt V (a * b) = mt V a * mt V b := by first | rfl | simp [Formalism.L2.Theta.mt]
  have key : mt V a * mt V b - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by noncomm_ring
  rw [hm, key, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ha i k]

end GlobalTheory.BigOn.Exp.TupLe.Swap
