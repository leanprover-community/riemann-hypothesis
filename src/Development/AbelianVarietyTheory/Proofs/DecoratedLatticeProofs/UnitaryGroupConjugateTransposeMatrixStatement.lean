module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupConjugateTransposeMatrix
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitary_group_conjugate_transpose_matrix : ∀ (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsFrame β I.L → ∃ G : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), ((Formalism.UG.bc (Formalism.L2.Herm.intAf I.F I.E).subtype G : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  first | exact @GlobalTheory.GramFrame.gram_frame_int | exact GlobalTheory.GramFrame.gram_frame_int | (intros; apply GlobalTheory.GramFrame.gram_frame_int <;> assumption)
