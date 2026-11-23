module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thG_unique_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  intro S G _ _ L ρ hL hρ g m R _ _ x K _ i hm hu hP th pt c c' H H'
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  obtain ⟨ρ₁, -, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw hL P.isLB hρ
  let T : Over (Sp R) := Over.mk (spMap i)
  let T₀ : Over S := Over.mk (spMap i ≫ x)
  have hτ : 𝟙 (Sp K) ≫ T₀.hom = T.hom ≫ x := Category.id_comp _
  obtain ⟨th₁, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp (T := T) (T₀ := T₀) (𝟙 _) hτ hw hL P.isLB th
  have hsq : pt.left ≫ G.hom = spMap i ≫ x := Over.w pt
  let x₁ : T ⟶ P.A := Over.homMk (hp.1.lift pt.left (spMap i) hsq) (hp.1.lift_snd _ _ _)
  have hx : 𝟙 (Sp K) ≫ pt.left = x₁.left ≫ α := by
    rw [Category.id_comp]; exact (hp.1.lift_fst _ _ _).symm
  have hn : x₁ ^ (m ^ 2) = 1 := by
    have h1 := GlobalTheory.ThetaPtMove.over_pow hp (T := T) (T₀ := T₀) (𝟙 _) hτ hx (m ^ 2)
    rw [H.1] at h1
    have h2 := GlobalTheory.ThetaPtMove.over_one hp (T := T) (T₀ := T₀) (𝟙 _) hτ
    exact Over.OverMorphism.ext (hp.1.hom_ext (h1.symm.trans h2) ((Over.w _).trans (Over.w _).symm))
  have hu' : IsUnit ((m ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    rw [Nat.cast_pow, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom m, ← map_pow]
    exact (hu.pow 2).map _
  have m1 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c)) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H
  have m2 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c')) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H'
  have e := ThG.unique (T := T) abelianSchemeLaws_all.1 P hm hu' m1 m2
  have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom e
  simpa using e2

end GlobalTheory.UMin
