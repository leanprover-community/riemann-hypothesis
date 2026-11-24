module

public import Formalism.PeriodIntegrals.HookBound
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility

theorem muStd_exists (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) : ∃ μ, PI.MuStd ν μ := by
  have hfg : (weyl ℤ N N le_rfl ν).FG :=
    (Formalism.L2.DIV.we_nabla_fg N N ν).of_le (weylLeDual ℤ N N le_rfl ν hν)
  have : Module.Finite ℤ (weyl ℤ N N le_rfl ν) := Module.Finite.iff_fg.mpr hfg
  let e := (Module.Free.chooseBasis ℤ (weyl ℤ N N le_rfl ν)).reindex (Fintype.equivFin _)
  have hmem : hw ℤ le_rfl ν ∈ weyl ℤ N N le_rfl ν := Submodule.subset_span ⟨[], rfl⟩
  have hne : (⟨hw ℤ le_rfl ν, hmem⟩ : weyl ℤ N N le_rfl ν) ≠ 0 := fun h0 =>
    hwNe ℤ N N le_rfl ν (congrArg Subtype.val h0)
  have : Nontrivial (weyl ℤ N N le_rfl ν) := nontrivial_of_ne _ _ hne
  exact ⟨_, _, e, Fin.pos_iff_nonempty.mpr e.index_nonempty, rfl⟩

end PI.SlopeSteps
