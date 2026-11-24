module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftSurjectiveKernelLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.tensor_lift_surjective_kernel_level : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)) ∧ ∀ z : TensorProduct (Ainf l) (Acris l) A.W, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _) z = 0 ↔ z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.tens_base_change | exact GlobalTheory.CompanionTheory.PerfFil.tens_base_change | (intros; apply GlobalTheory.CompanionTheory.PerfFil.tens_base_change <;> assumption)
