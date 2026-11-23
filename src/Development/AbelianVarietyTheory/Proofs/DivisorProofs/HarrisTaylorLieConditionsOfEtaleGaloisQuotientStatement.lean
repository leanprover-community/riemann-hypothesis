module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotient
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_lie_conditions_of_etale_galois_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (Ga : Type) [Group Ga] (ρ : Ga → (o.A.left ⟶ o.A.left)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover Ga ρ ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ A', IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A'), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  first | exact @GlobalTheory.UPel.HT.EtaleLie.lie_of_etale | exact GlobalTheory.UPel.HT.EtaleLie.lie_of_etale | (intros; apply GlobalTheory.UPel.HT.EtaleLie.lie_of_etale <;> assumption)
