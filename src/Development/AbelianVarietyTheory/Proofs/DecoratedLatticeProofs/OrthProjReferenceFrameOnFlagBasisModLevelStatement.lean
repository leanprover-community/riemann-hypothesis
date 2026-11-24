module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjReferenceFrameOnFlagBasisModLevel
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthProjReferenceFrame_on_flagBasis_mod_level : ∀ (D : D7) (X : HidaSetting D), (∀ y ∈ X.B.I.Lf, GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf) ∧ ∀ j : ℕ, flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf ∧ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) ∈ mL X.B.I X.B.g) ∧ (¬ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k) → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ mL X.B.I X.B.g) := by
  first | exact @GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL | exact GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL | (intros; apply GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL <;> assumption)
