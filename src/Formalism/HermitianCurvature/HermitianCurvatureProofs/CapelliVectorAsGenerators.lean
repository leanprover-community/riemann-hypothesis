module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cvag_posL_iff {k r : ℕ} (a b : Fin (Q.mdim k r 0)) : Q.posL k r 0 a = Q.posL k r 0 b ↔ a = b := by
  simp [Q.posL, Fin.ext_iff]

theorem cvag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : ℂ)
    (σ : Equiv.Perm (Fin (Q.mdim k r 0))) :
    (List.ofFn fun i : Fin (Q.mdim k r 0) =>
      Top (Q.EH (E := E) k r) (u - ((i : ℕ) : ℂ)) (Q.posL k r 0 (σ i)) (Q.posL k r 0 i)) =
      (capGens (zgCV k r) σ).map (fun gn => genOpR (E := E) gn u) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, Formalism.QuantumDeterminants.Top, genOpR, capGen, zgCV, Q.EH, EabH, cvag_posL_iff, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero]
  split_ifs <;> simp

theorem capelli_vector_as_generators : CVAsGens := by
  intro k r E _ _ Y f g
  simp only [Q.CV, Q.capL, qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cvag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
