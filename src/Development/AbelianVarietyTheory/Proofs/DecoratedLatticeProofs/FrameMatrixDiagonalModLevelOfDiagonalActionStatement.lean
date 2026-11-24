module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixDiagonalModLevelOfDiagonalAction
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

theorem _root_.GlobalTheory.T.frame_matrix_diagonal_mod_level_of_diagonal_action : ∀ (I : AutInst) (g : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (Y : I.Gf) (d : Fin I.n → Formalism.L2.Herm.intAf I.F I.E), IsLiftFrame I g b β → (∀ y ∈ I.Lf, I.fmat Y *ᵥ y ∈ I.Lf) → (∀ y ∈ I.Lf, I.fmat Y⁻¹ *ᵥ y ∈ I.Lf) → (∀ j : Fin I.n, I.fmat Y *ᵥ b j.val - (d j).1 • b j.val ∈ mL I g) → ∃ x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), frGL β x = (Y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∧ ∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - Matrix.diagonal d) i j).1 := by
  first | exact @GlobalTheory.FrameDiag.diag_mod_in_frame | exact GlobalTheory.FrameDiag.diag_mod_in_frame | (intros; apply GlobalTheory.FrameDiag.diag_mod_in_frame <;> assumption)
