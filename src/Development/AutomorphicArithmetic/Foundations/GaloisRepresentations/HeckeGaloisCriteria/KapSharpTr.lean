module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
public import Formalism.LocalRingCardinality.DataAmbForm
public import Formalism.LocalRingCardinality.DataKap
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (Λ : CutD D)



@[reducible] def sideTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) :
    RowSide (cut D Λ) EE := { S with }

section Side

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem downTo_tr (μ : D.what₂.Tup) (j : ℕ) : (sideTr Λ S).downTo μ j = S.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun f => f.comp (S.io μ j)) ih

theorem iota_tr (μ : D.what₂.Tup) : (sideTr Λ S).iota μ = S.iota μ := by
  unfold RowSide.iota; rw [downTo_tr]; rfl

theorem Qsp_tr (μ : D.what₂.Tup) : (sideTr Λ S).Qsp μ = S.Qsp μ := by
  unfold RowSide.Qsp RowSide.Usp; rw [iota_tr]; rfl

theorem RRset_tr (μ : D.what₂.Tup) : (sideTr Λ S).RRset μ = S.RRset μ := by
  unfold RowSide.RRset RowSide.LamSet; rw [iota_tr]; simp only [Qsp_tr]; rfl

theorem iiStar_tr : (sideTr Λ S).iiStar = S.iiStar := by
  have key : ∀ (f f' : S.Amb D.what₂.mu0 →ₗ[ℂ] EE) (Q Q' : Submodule ℂ (S.Amb D.what₂.mu0)), f = f' → Q = Q' →
      f.domRestrict Q ∘ₗ LinearMap.adjoint (f.domRestrict Q) = f'.domRestrict Q' ∘ₗ LinearMap.adjoint (f'.domRestrict Q') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact key _ _ _ _ (iota_tr Λ S _) (Qsp_tr Λ S _)

theorem kapOf_tr {n : ℕ} (ty : Fin n → D.what₂.FT) : (sideTr Λ S).kapOf ty = S.kapOf ty := by
  unfold RowSide.kapOf RowSide.kapRatio; rw [iiStar_tr]; rfl

theorem rrDef_tr (H : S.RRDef) : (sideTr Λ S).RRDef := by
  have e : (sideTr Λ S).RRset = S.RRset := funext (RRset_tr Λ S)
  unfold RowSide.RRDef; rw [e]; exact H

end Side

theorem kapSharp_tr : kapSharp (cut D Λ) = kapSharp D := kapOf_tr Λ (RowSide.sharp D) _

def ambTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (x : AmbForm D S) :
    AmbForm (cut D Λ) (sideTr Λ S) := { x with }

end UpperTheory.GalC
