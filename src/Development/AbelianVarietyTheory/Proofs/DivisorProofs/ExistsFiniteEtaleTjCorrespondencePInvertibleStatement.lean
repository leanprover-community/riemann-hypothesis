module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTjCorrespondencePInvertible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
theorem _root_.GlobalTheory.T.exists_finiteEtale_Tj_correspondence_p_invertible : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ T : TjCorr M.toRepFam r w j c, IsFinite T.s ∧ Etale T.s ∧ Surjective T.s ∧ IsFinite T.t ∧ Etale T.t ∧ ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ T.Y, y ≫ T.s = x ∧ ∃ (m₀ : ObjMap o₁ T.o y) (m₁ : ObjMap o₁' T.o' y), m₀.φ ≫ T.ψ.left = ψ₁.left ≫ m₁.φ := by
  first | exact @GlobalTheory.UPel.HT.ES.exists_tjCorr_finiteEtale | exact GlobalTheory.UPel.HT.ES.exists_tjCorr_finiteEtale | (intros; apply GlobalTheory.UPel.HT.ES.exists_tjCorr_finiteEtale <;> assumption)
