module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadratic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.exterior_differential_sign_rule_quadratic : StdD → (∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0) → WedgeQ := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ | exact GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ | (intros; apply GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ <;> assumption)
