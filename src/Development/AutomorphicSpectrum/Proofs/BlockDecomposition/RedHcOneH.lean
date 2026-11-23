module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SchFnPtTw
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisUnit

universe w w' u v u' v'

theorem pull_oneH {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w'} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  have e : m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0)))) =
      fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0))) :=
    funext fun s => h (s.obj (Fin.last 0))
  have c : ∀ s : ComposableArrows C' 1, (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A'.map (GlobalTheory.CatH.toLast i s)).hom 1 : A'.obj _) = 0 := by
    intro s
    rw [Fin.sum_univ_two, map_one, map_one]
    simp
  unfold CH.Mor.pull CH.oneH
  refine (CrystallineSemistableComparison.P.mapH_cls m.hom 0 _ _ ?_).trans ?_
  · rw [e]
    exact funext c
  · exact congrArg Submodule.Quotient.mk (Subtype.ext e)

theorem omMor_oneH {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}
    (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) :
    (omMor m σ₀ h).pull 0 (CH.oneH (OA L c)) = CH.oneH (OA L' c') :=
  pull_oneH _ _ _ fun _ => rfl

theorem redHc_oneH : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m), redHc F κ k h 0 (CH.oneH (OcA F κ k m)) = CH.oneH (OcA F κ k n) := by
  intro l _ O _ F κ k m n h
  exact omMor_oneH _ _ _

end GlobalTheory.CompanionTheory.CrisUnit
