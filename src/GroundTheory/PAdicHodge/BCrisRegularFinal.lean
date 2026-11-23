module

public import GroundTheory.PAdicHodge.BCrisGalois
public import GroundTheory.PAdicHodge.BCrisPlusInvariants
public import GroundTheory.PAdicHodge.BCrisRegularSenTate
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.PAdicHodge.BCrisEigen

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Module

variable {p : ℕ} [hp : Fact p.Prime]

namespace ACris

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)


include hζ in
theorem isUnit_of_galB_eigen {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
    {b : BCris hε} (hb0 : b ≠ 0)
    (hb : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], galB hε σ b = algebraMap ℚ_[p] (BCris hε) q * b) :
    IsUnit b :=
  isUnit_of_forall_galB_eq_mul hε hζ senTateCharacters hb0 hb


variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)

end ACris

end GroundTheory.PAdicHodge
