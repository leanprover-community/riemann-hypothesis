module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem inCC_wordSum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m n : ℕ}
    {F : B.Mat k r → E} (hF : B.InCC A (m + n) F) :
    ∀ L : List (ℂ × List (B.Mat k r)), (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ n) →
      B.InCC A m (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum) := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simpa using (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (k := k) (r := r) (E := E) (A := A) (m := m))⟩
  | cons cw L ih =>
    intro hL
    have h1 : B.InCC A m (fun g => cw.1 • B.Rw cw.2 F g) := by
      have hw := hL cw (by simp)
      have h0 : B.InCC A (m + cw.2.length) F :=
        Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono le_rfl (by omega) hF
      obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw (fun X hX => (hw.1 X hX).1) h0
      exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul cw.1 hc⟩
    have h2 := ih (fun cw' hcw' => hL cw' (List.mem_cons_of_mem cw hcw'))
    obtain ⟨c₁, hc₁⟩ := h1
    obtain ⟨c₂, hc₂⟩ := h2
    refine ⟨c₁ + c₂, ?_⟩
    simpa [List.map_cons, List.sum_cons] using Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc₁ hc₂

theorem coefficient_vector_in_L2_class : CVInCC := by
  intro k r E _ _ A m F Y s hF
  obtain ⟨L, hLw, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  have hck : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F := by
    obtain ⟨c, hc⟩ := hF
    exact Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast Nat.le_add_left _ _) hc.1
  obtain ⟨c, hc⟩ := inCC_wordSum hF L hLw
  refine ⟨_, Formalism.FourierDecayAlt.P.Qx8.CCle_congr (f := fun g => s • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum) ?_
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul s hc)⟩
  intro g hg
  rw [Pi.smul_apply, hCV E (B.GV k r) F hck g hg hg]

end Formalism.FourierDecayAlt.P.CutMP.En
