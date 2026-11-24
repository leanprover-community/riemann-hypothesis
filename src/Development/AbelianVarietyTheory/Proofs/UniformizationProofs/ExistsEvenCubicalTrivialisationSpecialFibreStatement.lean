module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibre
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (P : CP G) (w : G ⟶ G), IsMonHom w → LBIso P.L.L (cubeLB G ![𝟙 G, w] P.L.L) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q₀ : TQ (thickObj V (maximalIdeal V) 0 G) X) (P₀ : CP (thickObj V (maximalIdeal V) 0 G)), IsLevelCP (maximalIdeal V) 0 P₀ P → ∃ σ : CubTriv P₀.c Q₀.i, σ.Even := by
  first | exact @GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre | exact GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre | (intros; apply GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre <;> assumption)
