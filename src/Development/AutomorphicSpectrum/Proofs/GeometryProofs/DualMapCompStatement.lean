module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_uniform_height_constant_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o₀ : RootOrigin Y ∅ R Fx), ∃ C₀ : ℝ, ∀ (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y S M Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich o.𝔐 p κ) → ∀ r, Ht.VertBound (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (o₀.e r) / o.e r) (C₀ + ∑ p ∈ S, ((if p = 2 then 2 else 1 / ((p : ℝ) - 1)) + 2 * padicValInt p (discr E)) * Real.log p) := by
  exact @GlobalTheory.CompanionTheory.Ar.OrVert.or_vert
