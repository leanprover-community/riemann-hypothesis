module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexAutomorphismWeierstrassTorsionQCoeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedWeierstrassPTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ConjExp


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.ConjExp.qConj_torsion : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wp N x) (_root_.GlobalTheory.WpFam.wp N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wpd N x) (_root_.GlobalTheory.WpFam.wpd N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ (x ≠ 0 → _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wB N x) (_root_.GlobalTheory.WpFam.wB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)))) := by
  intro N _ g a hg x
  have hc := _root_.GlobalTheory.WpFam.CoeffConj.main N g a hg x
  refine ⟨⟨_, _root_.GlobalTheory.WpFam.ExpP.main N x, ?_⟩,
    ⟨_, _root_.GlobalTheory.WpFam.DerivExpansion.main N x, ?_⟩, fun hx => ⟨_,
      _root_.GlobalTheory.WpFam.ExpansionB.main N x hx, ?_⟩⟩
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cP N x n)) = _root_.GlobalTheory.WpFam.cP N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.2.2]
    exact _root_.GlobalTheory.WpFam.ExpP.main N _
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cD N x n)) = _root_.GlobalTheory.WpFam.cD N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.1]
    exact _root_.GlobalTheory.WpFam.DerivExpansion.main N _
  · have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
    rw [show (fun n => g (_root_.GlobalTheory.WpFam.cB N x n)) = _root_.GlobalTheory.WpFam.cB N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).1]
    exact _root_.GlobalTheory.WpFam.ExpansionB.main N _ fun h => hx (hzero.1 h)

end GlobalTheory.WpFam.ConjExp
