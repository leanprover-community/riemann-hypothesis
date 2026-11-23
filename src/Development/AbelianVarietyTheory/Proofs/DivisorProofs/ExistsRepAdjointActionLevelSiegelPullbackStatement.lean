module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullback
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_rep_adjointAction_level_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (E : Scheme.{0}) (πE : E ⟶ S) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ c.A.left) (φ₂E : (G2 AE).left ⟶ (G2 c.A).left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsLocallyNoetherian E ∧ IsFinite πE ∧ IsGrpPullback AE c.A πE φE ∧ IsSquare φE φ₂E ∧ RosatiFor D actE (c.P.pull φ₂E) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ (∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actE.act a).left) ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_rosati_level) | (exact GlobalTheory.UPel.HT.exists_finite_rep_rosati_level) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_rosati_level  <;> assumption)
