module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.starSubdivisionDepth_hostFixingAut_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ w : InvFun (𝓞 E)), IsTwInv H ψ → IsTwInv H w → IsTwInv H (starDepth H.bar ψ w) := by
  first | exact @GlobalTheory.PolFan.isTwInv_starDepth | exact GlobalTheory.PolFan.isTwInv_starDepth | (intros; apply GlobalTheory.PolFan.isTwInv_starDepth <;> assumption)
