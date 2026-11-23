module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Mathlib.Topology.LocallyConstant.Basic
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem contAction_levRepZ_of_isLocallyConstant
    {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (hloc : ∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) :
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
  unfold ReciprocityTheory.Gal.ContAction
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨g₀, x₀⟩
  have hx := hloc x₀.val (Lev.smul_val x₀)
  refine ⟨{g | ρ g x₀.val = ρ g₀ x₀.val} ×ˢ {x₀},
    (hx.isOpen_fiber _).prod (isOpen_discrete _), ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨g, x⟩ ⟨hg, hx'⟩
  simp only [Set.mem_singleton_iff] at hx'
  subst hx'
  apply Lev.ext
  show (levRep ρ c g x).val = (levRep ρ c g₀ x).val
  rw [levRep_val, levRep_val]
  exact hg

end GlobalTheory.ShapeNeg
