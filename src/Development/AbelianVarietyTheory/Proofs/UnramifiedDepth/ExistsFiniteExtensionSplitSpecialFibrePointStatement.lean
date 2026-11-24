module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtensionSplitSpecialFibrePoint
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
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_finite_extension_split_special_fibre_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ t : SAB H (Sp V), GlobalTheory.LN.PolAt t (Out.jK V) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (β : V →+* Ω), (∀ a ∈ maximalIdeal V, β a = 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V →+* W) (β' : W →+* Ω) (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap f)), GlobalTheory.LN.CDvr W ∧ β'.comp f = β ∧ (∀ a ∈ maximalIdeal W, β' a = 0) ∧ GlobalTheory.LN.PolAt t' (Out.jK W) ∧ GlobalTheory.LN.SplitOver t'.G (maximalIdeal W) := by
  first | exact @GlobalTheory.SplitPoint.exists_split_extension | exact GlobalTheory.SplitPoint.exists_split_extension | (intros; apply GlobalTheory.SplitPoint.exists_split_extension <;> assumption)
