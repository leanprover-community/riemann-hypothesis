module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulIdemFromCenter
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.Pass.CentralStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem main : StepCentral := by
  intro _ D P i s
  classical
  have hcard : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g D.nd) := by
    rw [D.nd.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change _ = ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
    rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]
  haveI : Finite (G0g D.nd) := Nat.finite_of_card_ne_zero (hcard ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  have key : ∀ L : List (Σ k : Fin 2, D.nd.PlG k),
      let e := (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod
      e * e = e ∧ ∀ z, e * z = z * e := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      obtain ⟨h1, h2⟩ := ih
      have hc := Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D a.1 a.2 _
        (D.ntypes.eSer_central a.1 (s a)))
      have hi : ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) * ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) =
          ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) := by
        rw [GlobalTheory.SeriesSupportTest.atPlace_eq, ← map_mul, D.ntypes.eSer_idem]
      simp only [List.map_cons, List.prod_cons]
      refine ⟨?_, fun z => ?_⟩
      · rw [mul_assoc, ← mul_assoc _ (ArithmeticCylinders.atPlace D a.1 a.2 _), hc, mul_assoc, h1, ← mul_assoc, hi]
      · rw [mul_assoc, h2, ← mul_assoc, ← hc, mul_assoc]
  obtain ⟨h1, h2⟩ := key Finset.univ.toList
  obtain ⟨ζ, hζ⟩ := P.zetaPrimitiveRoot i
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  obtain ⟨z, hz, hz'⟩ := GlobalTheory.CentralIdem.card_mul_idem_from_center D i (G0g D.nd) _ h1 h2
    ⟨ζ, hcard ▸ hζ.map_of_injective hinj⟩
  refine ⟨⟨z, hz⟩, Finset.univ.toList, Finset.nodup_toList _, by simp, ?_⟩
  ext h
  rw [hcard]
  simpa [PairedCharacterCondition.mapCoef] using hz' h

end GlobalTheory.Pass.CentralStep

end
