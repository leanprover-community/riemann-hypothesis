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

theorem crag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun i : Fin k => fun y : Q.Mx k r → E =>
      (if id (σ i) = id i then (w - ((i : ℕ) : ℂ)) • y else 0) +
        Q.RZ (Hpk k r) (Q.unitB (Hpk k r) Bs (id (σ i)) (id i)) y) =
      (capGens (zgB Bs) σ).map (fun gn => genOpR (E := E) gn w) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, genOpR, capGen, zgB, Q.RZ, id, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, Pi.add_apply]
  split_ifs <;> simp

theorem right_capelli_as_generators : CapRAsGens := by
  intro k r E _ _ Bs w f g
  simp only [Q.capR, Q.qmF, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [crag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
