module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLowestKTypeOfExtremalVectorCase
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.realLowestKType_of_extremalVectorCase : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), Formalism.IndefR.FWT.IsExtVec (R.MW i (sg0 D A)) (fun ρ => ((v ρ : (R.MW i (sg0 D A)).sm ρ))) → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) → RealLow R i t := by
  first | exact @GlobalTheory.RawLift.RealLowRed.realLow_of_ext | exact GlobalTheory.RawLift.RealLowRed.realLow_of_ext | (intros; apply GlobalTheory.RawLift.RealLowRed.realLow_of_ext <;> assumption)
