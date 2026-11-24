module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroRight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.restriction_product_rank_zero_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i n : ℕ) (π₁ : GRep k (i + 1)) (π₂ : GRep k 0) (h : (i + 1) + 0 = n + 1) (h' : i + 0 = n), IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodPGn (gres π₁) π₂)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero | exact GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero | (intros; apply GlobalTheory.CompanionTheory.LeibTrivBlock.miso_gres_prod_zero <;> assumption)
