module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierNegativeVectorTermNear
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_coprime_multiplier_negativeVector_term_near : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) - hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := by
  first | exact @GlobalTheory.ScalW.znear_term | exact GlobalTheory.ScalW.znear_term | (intros; apply GlobalTheory.ScalW.znear_term <;> assumption)
