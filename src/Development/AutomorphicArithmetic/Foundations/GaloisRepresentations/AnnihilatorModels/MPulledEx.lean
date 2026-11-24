module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledEx_of :
    ObjTri → PullIsog → PullKer → PulledEx := by
  intro hTri hIsog hKer p _ D R _ b N hN hc M r w j c T S x σ hx o₁ m₁ y hy
  obtain ⟨m₀, htri⟩ := (hTri p D R b N hN hc S T.Y M.X σ (T.s ≫ M.s) M.s o₁ T.o M.univ y T.s).2 x hy m₁ T.ms
  have hσ : y ≫ T.s ≫ M.s = σ := by rw [← Category.assoc, hy, hx]
  obtain ⟨o', m', ψ, hisog, hsq⟩ := hIsog p D R b N T.Y S (T.s ≫ M.s) σ y hσ c T.o T.o' T.ψ T.isog o₁ m₀
  have htj := (hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ o' m₀ m' T.ψ ψ hsq).2 r w j T.tj
  exact ⟨⟨o', ψ, m₀, m', hsq, htri, hisog, htj⟩⟩
