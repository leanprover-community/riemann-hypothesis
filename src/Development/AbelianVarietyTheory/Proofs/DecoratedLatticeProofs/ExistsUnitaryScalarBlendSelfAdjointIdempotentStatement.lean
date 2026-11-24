module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryScalarBlendSelfAdjointIdempotent
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
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitary_scalarBlend_selfAdjoint_idempotent : ∀ (I : AutInst) (P : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (c : I.E ⊗[I.F] Af I.F), (∀ y, P *ᵥ (P *ᵥ y) = P *ᵥ y) → (∀ x y, hA I (P *ᵥ x) y = hA I x (P *ᵥ y)) → c * sigA I c = 1 → ∃ h : I.Gf, I.fmat h = c • 1 + (1 - c) • P ∧ I.fmat h⁻¹ = sigA I c • 1 + (1 - sigA I c) • P := by
  first | exact @GlobalTheory.unitTorus_unit | exact GlobalTheory.unitTorus_unit | (intros; apply GlobalTheory.unitTorus_unit <;> assumption)
