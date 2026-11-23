module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FibreTorsion

theorem card_torsion_of_proper_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (F : Type) [Field F] [IsAlgClosed F] (p : Sp F ⟶ S), IsProper (pullback.snd G.hom p) → ∀ N : ℕ, (N : F) ≠ 0 → Nat.card {x : Over.mk p ⟶ G // x ^ N = 1} = N ^ (2 * g) := by
  intro S G _ _ hG g hg F _ _ p hprop N hN
  let B := (Over.pullback p).obj G
  haveI : IsProper B.hom := hprop
  have hB : IsAbelianScheme B :=
    AbelianSchemeGerms.isAbelianScheme_of_proper B (IsSemiAbelian.pullback p G hG)
  have hg' : SmoothOfRelativeDimension g B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional F B g N hB hg' hN
  have hp := isGrpPullback_pullback G p
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp F)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst G.hom p = y.left ≫ pullback.fst G.hom p := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp F))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Nat.card {x : Over.mk ((𝟙_ (Over (Sp F))).hom ≫ p) ⟶ G // x ^ N = 1} = N ^ (2 * g) := by
    rw [← h]
    refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
    show x ^ N = 1 ↔ e x ^ N = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp F))).hom ≫ p = p := Category.id_comp p
  rw [h3] at h2
  exact h2

end GlobalTheory.FibreTorsion
