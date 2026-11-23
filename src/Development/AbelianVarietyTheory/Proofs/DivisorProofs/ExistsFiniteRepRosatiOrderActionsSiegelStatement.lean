module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepRosatiOrderActionsSiegel
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_finite_rep_rosati_orderActions_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (c : SiegPre h M ζ s₁), Out.RelAmple c.A c.diag → ∃ (H : Scheme.{0}) (πH : H ⟶ S) (AH : Over H) (_ : GrpObj AH) (_ : IsCommMonObj AH) (φH : AH.left ⟶ c.A.left) (φ₂H : (G2 AH).left ⟶ (G2 c.A).left) (actH : OActN D.O AH), IsFinite πH ∧ IsAbelianScheme AH ∧ IsGrpPullback AH c.A πH φH ∧ IsSquare φH φ₂H ∧ RosatiFor D actH (c.P.pull φ₂H) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → ∃! z : T ⟶ H, z ≫ πH = g ∧ ∃ ψ : AT.left ⟶ AH.left, IsGrpPullback AT AH z ψ ∧ ψ ≫ φH = φ ∧ ∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actH.act a).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (exact GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati  <;> assumption)
