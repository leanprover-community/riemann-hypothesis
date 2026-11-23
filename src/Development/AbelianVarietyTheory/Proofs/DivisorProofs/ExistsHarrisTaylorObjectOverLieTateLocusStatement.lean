module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOverLieTateLocus
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

theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_over_lieTate_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∀ (Z : Scheme.{0}) (j : Z ⟶ X), (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z), x ≫ j ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ j)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z) (β : R →+* k), x ≫ j ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ j)) → ∃ (u : Obj b N ((j ≫ πX) ≫ t)) (ψ : u.A.left ⟶ AX.left) (ψ₂ : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A AX j ψ ∧ IsSquare (ψ ≫ φX) ψ₂ ∧ LBIso u.P (c.P.pull ψ₂) ∧ (∀ a : D.O, (u.act.act a).left ≫ ψ = ψ ≫ (actX.act a).left) ∧ ∀ y, (u.eta y).left ≫ ψ = j ≫ (ηX y).left := by
  first | (exact @GlobalTheory.HTMkObj.exists_obj_of_locus) | (exact GlobalTheory.HTMkObj.exists_obj_of_locus) | (intros; apply GlobalTheory.HTMkObj.exists_obj_of_locus <;> assumption)
