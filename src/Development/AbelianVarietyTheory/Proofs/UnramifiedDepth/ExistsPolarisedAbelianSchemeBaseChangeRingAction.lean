module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_polBaseChange_oAct : ∀ (T O : Type) [CommRing T] [CommRing O] (io : T →+* O) (P₀ : Out.PolAV (Geo.Tor.Sp T)), ∃ (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ ∧ Geo.Tor.LBIso P.L (P₀.L.pull φ) ∧ P.g = P₀.g ∧ ∀ (OE : Type) [CommRing OE] [StarRing OE] (o₀ : P₀.OAct OE), ∃ o : P.OAct OE, ∀ a, (o.act a).left ≫ φ = φ ≫ (o₀.act a).left := by
  intro T O _ _ io P₀
  obtain ⟨P, φ, hφ, hg, hm, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (Geo.Tor.spMap io) P₀
  have gp : Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ := ⟨hφ, fun U x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y),
      ← hm]
    rfl⟩
  exact ⟨P, φ, gp, Geo.Tor.LBIso.symm ⟨t, ht⟩, hg, fun OE _ _ o₀ => Geo.Tor.polOActPull _ _ _ P₀ P φ gp ⟨t, ht⟩ OE o₀⟩

end GlobalTheory
