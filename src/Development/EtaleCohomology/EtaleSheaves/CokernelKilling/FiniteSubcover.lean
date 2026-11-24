module

public import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.KillCokPf.Lem

theorem et_isOpenMap {D D₁ : CommRingCat.{0}} (e : D ⟶ D₁) (he : Et e) : IsOpenMap (PrimeSpectrum.comap e.hom) := by
  letI := e.hom.toAlgebra
  haveI : Algebra.Etale D D₁ := he
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := D) (S := D₁)

theorem finite_subcover {D : CommRingCat.{0}} (D₁ : PrimeSpectrum D → CommRingCat.{0}) (e : ∀ r, D ⟶ D₁ r)
    (he : ∀ r, Et (e r)) (hr : ∀ r, r ∈ Set.range (PrimeSpectrum.comap (e r).hom)) :
    ∃ s : Finset (PrimeSpectrum D), ∀ x : PrimeSpectrum D, ∃ r ∈ s, x ∈ Set.range (PrimeSpectrum.comap (e r).hom) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun r => Set.range (PrimeSpectrum.comap (e r).hom))
    (fun r => (et_isOpenMap (e r) (he r)).isOpen_range) (fun x _ => Set.mem_iUnion.2 ⟨x, hr x⟩)
  refine ⟨s, fun x => ?_⟩
  have := hs (Set.mem_univ x)
  simp only [Set.mem_iUnion] at this
  obtain ⟨r, hrs, hx⟩ := this
  exact ⟨r, hrs, hx⟩

end LateralTheory.E.KillCokPf.Lem
