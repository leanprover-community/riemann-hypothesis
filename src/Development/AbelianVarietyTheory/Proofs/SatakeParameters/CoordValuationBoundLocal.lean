module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.UPel.HT.GenProj

def baseOfGBase {p : ℕ} [Fact p.Prime] {D : Datum p} (gb : GBase D.toG ℂ) : Base D ℂ where
  unit k hk := by
    refine isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr ?_)
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.mp hk)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    haveI : CharZero k := (RingHom.charZero_iff β.injective).mp inferInstance
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (CharP.cast_eq_zero k p)

theorem isProjOver_genModel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.CompactB → ∀ (gb : GBase D.toG ℂ) (N : ℕ),
    3 ≤ N → N.Coprime p → ∀ X : GenModel gb N, IsProjOver X.s := by
  intro p _ D hC gb N hN hNp X
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D ℂ (baseOfGBase gb) N hN hNp
  have hM : IsProjOver M.s := GlobalTheory.UPel.HT.Model.isProjOver_of_compactB p D ℂ (baseOfGBase gb) N hN hNp hC M
  obtain ⟨j, _, hj, hjs, _⟩ := GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre p D ℂ (baseOfGBase gb) ℂ (RingHom.id ℂ) gb rfl (fun _ => rfl) N hN hNp M X
  rw [← hjs]
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion j (GlobalTheory.ProjSpace.isProjOver_pullback_snd (RingHom.id ℂ) hM)

end GlobalTheory.UPel.HT.GenProj
