module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfOverTwo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.MuUnrTie
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    GlobalTheory.HubX.MuUnr D := by
  intro _ hL D P i hl w hw
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, lt_of_lt_of_le (Nat.sub_lt hj.1 Nat.zero_lt_one) hj.2⟩
  have hjj : j.1 + 1 = D.nd.j i := Nat.sub_add_cancel hj.1
  have hlp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  rw [P.chr.unr_iff, P.chr.tw, P.chr.muC i j hjj, P.chr.etaTinv]
  refine GlobalTheory.MuTameQS.unrAt_mul ?_ (unrAt_inv (P.cf.isEta.unr w))
  unfold TupTied.tup
  refine GlobalTheory.MuTameQS.unrAt_mul ?_ ?_
  · refine (P.cf.isMu0 j).unr w fun k hk => ?_
    have e := eq_of_over_two hlp (D.host.g_prime k) w hw hk
    apply hl
    rw [e]
    fin_cases k <;> simp [TwistedPlaces.gset]
  · rw [D.nd.mu_w i, P.tp.xi_tw, D.nd.w_l i]
    refine GlobalTheory.MuTameQS.unrAt_mul ?_ ?_
    · unfold CharFrame.delAt
      split_ifs with h
      · refine P.cf.isDel'.unr w fun ho => D.host.pde_ne ?_
        rw [← h]
        exact eq_of_over_two hlp D.host.pde'_prime w hw ho
      · refine P.cf.isDel.unr w fun ho => h ?_
        exact eq_of_over_two hlp D.host.pde_prime w hw ho
    · have hpsi := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
      rw [D.nd.w_l i, ← P.Q_eq i] at hpsi
      exact (hpsi.ram w).2 fun hq => D.nd.SQ_l i w (Or.inr hq) hw
end GlobalTheory.MuUnrTie
end
