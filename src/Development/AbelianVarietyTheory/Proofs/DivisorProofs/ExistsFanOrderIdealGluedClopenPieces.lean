module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.Poinc

theorem stalkId_finsetProd {X : Scheme.{0}} {ι : Type} (s : Finset ι) (K : ι → X.IdealSheafData) (x : X) :
    FinalTheorems.stalkId (∏ c ∈ s, K c) x = ∏ c ∈ s, FinalTheorems.stalkId (K c) x := by
  classical
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  simp only [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x ⟨U, hU⟩ hx]
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.prod_insert hc, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul, ih]

theorem stalkId_prodPow {X : Scheme.{0}} {ι : Type} [Fintype ι] (K : ι → X.IdealSheafData) (e : ι → ℕ) (x : X) :
    FinalTheorems.stalkId (∏ c, K c ^ e c) x = ∏ c, FinalTheorems.stalkId (K c) x ^ e c := by
  rw [stalkId_finsetProd]
  simp only [GlobalTheory.Vanishing.stalkId_pow]

end GlobalTheory.Poinc
