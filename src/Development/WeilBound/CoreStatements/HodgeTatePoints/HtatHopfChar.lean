module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopf
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFlat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrimeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroupStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtBaseChangeStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.SectionCharValues

theorem exists_section_hasValues_char (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T]
      (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) := by
  intro R _ _ _ _ T _ _ Γ χ
  have hA := PositivityTheory.HtPt.Htat.HopfOrderTop.btOrder_top_isHopfOrder hHenselian hBaseChange hRegular R T Γ
  have hm := char_mem_hopfOrder R T _ hA χ
  obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Htat.ValuationInjectivePi.mem_btOrder_iff Γ _).mp hm 1
  refine ⟨s, fun t => ?_⟩
  exact (hs t _).trans (by simp)

end PositivityTheory.HtPt.Htat.SectionCharValues

theorem PositivityTheory.HtPt.Htat.ht_char_section_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) :=
  @PositivityTheory.HtPt.Htat.SectionCharValues.exists_section_hasValues_char hHenselian hBaseChange hRegular
