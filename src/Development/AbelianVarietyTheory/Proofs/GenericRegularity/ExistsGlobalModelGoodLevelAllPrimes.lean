module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Reg.modelAt_and_nonempty_global_model : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 →
    (∀ la, _root_.GlobalTheory.Reg.ModelAt Xo c la) ∧
      Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) := by
  classical
  intro E _ _ _ H Dw l Xo c hpq hgood hA
  obtain ⟨hGI, hQH⟩ := _root_.GlobalTheory.Moduli.jointExistence_and_moduliScheme
  have hne : ∀ l' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l') := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1ab at hQH
    exact fun l' => hQH E H Dw l' hpq
  let family : (l' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l' :=
    Function.update (fun l' => Classical.choice (hne l')) l Xo
  have hfam : family l = Xo := Function.update_self _ _ _
  refine ⟨fun la => ?_, ?_⟩
  · have h := _root_.GlobalTheory.Reg.modelAt_of_good_level hGI E H Dw hpq family l c la
      (fun p hp _ => hgood p hp)
    rwa [hfam] at h
  · have hGI' := hGI
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PartI at hGI'
    obtain ⟨Y, -, hY⟩ := hGI'.2 E H Dw hpq family
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N6 at hY
    obtain ⟨Ygl, -⟩ := hY l c hgood hA
    rw [hfam] at Ygl
    exact ⟨Ygl⟩

end GlobalTheory.Reg
