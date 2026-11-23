module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.GoodModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Models GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem hecke_rank_zero (hD : D.p + D.q = 0) : ToroidalHeckeCompatibility (H := H) (D := D) := by
  intro l Xo 𝔓 p i _ _ _ _ _ k _ _ y C _
  obtain ⟨hs, hG⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  refine ⟨y, ⟨rfl, 𝟙 _, MonoidHom.id _, Category.id_comp _, fun x => Category.comp_id _, fun _ _ => rfl,
    Function.surjective_id, ?_, fun n x x' c _ h => ?_, fun p' _ a => ⟨hom_unique hG _ _, hom_unique hG _ _⟩⟩,
    fun y'' h => (cancel_mono Xo.s).1 h.1⟩
  · ext x
    rw [hom_unique hG x 1]
    exact ⟨fun _ => C.one_mem, fun _ => (MonoidHom.id _).ker.one_mem⟩
  · have h₁ := weilIs_zero hG Xo.univ.t.PP.isLB (triv_rig hG Xo.univ.t.PP) (n : ℤ) x x'
    have e := GlobalTheory.CommutatorPairing.weilIs_unique globalFns_holds (isAbelianScheme_zero hG) Xo.univ.t.PP.isLB h h₁
    have e' : unitOn (c ^ p ^ 2) = 1 := by
      have : unitOn (c ^ p ^ 2) = unitOn c ^ p ^ 2 := map_pow _ _ _
      rw [this, e, one_pow]
    rw [e']
    exact h₁

end GlobalTheory.CompanionTheory.Ar.Top.GoodModel
