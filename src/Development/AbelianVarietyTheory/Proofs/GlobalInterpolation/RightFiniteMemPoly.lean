module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePointsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemOfFiniteDimensionalSpanRightTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryCoordinateAlgebraDenseStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem rightFinite_mem_poly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (f : infU E n → ℂ), Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => fun x : infU E n => f (x * k))) → f ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} := by
  intro E _ _ _ n f hf hfin
  haveI := GlobalTheory.T.compactSpace_definiteUnitaryInfinitePoints E n
  obtain ⟨hc, hs, hsep, hinv, hcop⟩ := GlobalTheory.T.unitary_coordinate_algebra_dense E n
  haveI : T2Space (infU E n) := ⟨fun x y hxy => by
    obtain ⟨p, hp, hne⟩ := hsep x y hxy
    exact separated_by_continuous (hc p hp) hne⟩
  refine GlobalTheory.T.mem_of_finiteDimensional_span_rightTranslates' (infU E n) (Algebra.adjoin ℂ _) hc hs hsep ?_ f hf hfin
  intro p hp
  obtain ⟨m, a, b, hab, heq⟩ := hcop p hp
  refine ⟨m, fun i x => a i x⁻¹, b, fun i => ⟨hinv _ (hab i).1, hc _ (hab i).2⟩, ?_⟩
  intro x k
  exact heq x⁻¹ k

end GlobalTheory.UnitaryBC
