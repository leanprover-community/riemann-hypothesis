module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FivePointLawsTrueChains
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

theorem _root_.GlobalTheory.T.fivePointLaws_trueChains :
    ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn →
    ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι),
      ∃ Bd : Built.Dat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u,
        Bd.ch = tw (I.tw l l0 Z) u a ∧
        (∀ i, i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m →
          letI : NumberField Bd.E := Bd.nE
          Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧
        (∀ i, i < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m →
          ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧
        Bd = dat I l Z u a := by
  exact GlobalTheory.LvT.Built.TrueLaws.laws_true_fam
