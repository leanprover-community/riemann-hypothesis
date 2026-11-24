module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameExpansionThickeningOpen
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.eq_of_same_expansion_thickening_open : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens) (hW : W ≤ (fstG I e G).left ⁻¹ᵁ secChart U.LG.L i') (g : Γ((thickObj R I e G).left, W)), U.ExpandsAt e k σ f → GlobalTheory.MumMult.ChartExpOn U e k i' W g f → ((thickObj R I e G).left.presheaf.map (homOfLE hW).op).hom (((fstG I e G).left.app (secChart U.LG.L i')).hom (σ.f i')) = g := by
  first | exact @GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn | exact GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn | (intros; apply GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn <;> assumption)
