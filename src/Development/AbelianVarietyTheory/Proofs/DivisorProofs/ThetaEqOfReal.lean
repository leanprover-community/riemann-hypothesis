module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
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

open NumberField Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem theta_eq_of_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), IsStdChar D ψ (-1) →
    ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      (∀ w : WO V W, w.map (finPart D) = 0 → f w = f' w) → f = f' := by
  intro D ψ V W _ f f' hf hf' h
  have h0 : f + (-1 : ℂ) • f' = 0 := GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real
    (GlobalTheory.WeilVacMove.isTheta_add hf (GlobalTheory.WeilVacMove.isTheta_smul (-1) hf')) fun w hw => by
      rw [Pi.add_apply, Pi.smul_apply, h w hw, neg_one_smul, add_neg_cancel]
  rwa [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0

end GlobalTheory.AdTh
