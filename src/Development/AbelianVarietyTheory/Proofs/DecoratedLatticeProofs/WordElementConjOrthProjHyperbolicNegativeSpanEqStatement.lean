module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WordElementConjOrthProjHyperbolicNegativeSpanEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wordElement_conj_orthProjHyperbolicNegativeSpan_eq : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : VA X.B.I), X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y) = ∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a + ∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) := by
  first | exact @GlobalTheory.ScalW.Conj.prj_conj | exact GlobalTheory.ScalW.Conj.prj_conj | (intros; apply GlobalTheory.ScalW.Conj.prj_conj <;> assumption)
