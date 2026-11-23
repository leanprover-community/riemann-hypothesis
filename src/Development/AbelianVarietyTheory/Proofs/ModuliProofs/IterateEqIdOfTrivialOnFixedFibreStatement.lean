module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IterateEqIdOfTrivialOnFixedFibre
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.iterate_eq_id_of_trivial_on_fixed_fibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → ∀ g : D.La →ₗ[𝓞 E] D.La, (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x → (fun f : Xo.X ⟶ Xo.X => f ≫ r.hom)^[l.A] (𝟙 _) = 𝟙 _ := by
  first | exact @GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre | exact GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre | (intros; apply GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre <;> assumption)
