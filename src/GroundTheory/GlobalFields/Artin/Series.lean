module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField Filter Topology ComplexConjugate

namespace GroundTheory.Global


variable {G : Type*} [Group G]


variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]


variable (v : HeightOneSpectrum (𝓞 K))






section Convergence

omit [IsGalois K L] in
theorem exists_norm_le (f : Gal(L/K) → ℂ) : ∃ C, ∀ g, ‖f g‖ ≤ C := by
  classical
  have := Fintype.ofFinite Gal(L/K)
  exact ⟨∑ g, ‖f g‖, fun g => Finset.single_le_sum (fun x _ => norm_nonneg (f x))
    (Finset.mem_univ g)⟩

end Convergence

section Holomorphy

end Holomorphy

section Additivity

end Additivity

section Conjugation

end Conjugation

end GroundTheory.Global
