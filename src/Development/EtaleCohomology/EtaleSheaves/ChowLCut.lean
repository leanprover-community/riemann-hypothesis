module

public import Development.EtaleCohomology.EtaleSheaves.ChowCut
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowLCut

inductive IterLine {S : Scheme.{0}} : ∀ {Y : Scheme.{0}}, (Y ⟶ S) → Prop
  | iso {Y : Scheme.{0}} (e : Y ⟶ S) : IsIso e → IterLine e
  | comp {Y T : Scheme.{0}} (l : Y ⟶ T) (k : T ⟶ S) : IsLine l → IterLine k → IterLine (l ≫ k)

theorem IT_of_iterLine {S Y : Scheme.{0}} {k : Y ⟶ S} (hk : IterLine k) :
    ∀ {X : Scheme.{0}} (u : X ⟶ Y), IsIntegralHom u → IT (u ≫ k) := by
  induction hk with
  | iso e he => intro X u hu; exact IT.int _ (by infer_instance)
  | comp l k hl _ ih =>
    intro X u hu
    refine IT.step (u ≫ l) k _ ?_ ⟨_, u, l, hu, hl, rfl⟩ (Category.assoc _ _ _)
    simpa using ih (𝟙 _) inferInstance

def LineEx : Prop := ∀ S : Scheme.{0}, ∃ (L : Scheme.{0}) (l : L ⟶ S), IsLine l

def IterBC : Prop := ∀ {P S X : Scheme.{0}} (q : P ⟶ S) (g : X ⟶ S), IterLine q → IterLine (pullback.fst g q)

def ChowGraph : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A)) (X' : Scheme.{0}) (i : X' ⟶ pullback p₁ q)
    (U : X₁.Opens) (s : U.toScheme ⟶ X'), IterLine q ∧ IsClosedImmersion i ∧ IsClosedImmersion (i ≫ pullback.snd p₁ q) ∧
    (U : Set X₁).Nonempty ∧ s ≫ i ≫ pullback.fst p₁ q = U.ι

theorem goal_of (hB : IterBC) (hG : ChowGraph) : LateralTheory.E.ChowCut.ChowL := by
  intro A _ X₁ p₁ _ hX₁
  obtain ⟨P, q, X', i, U, s, hq, hi, his, hU, hs⟩ := hG A p₁ hX₁
  refine ⟨X', i ≫ pullback.fst p₁ q, U, s, hU, hs, IT_of_iterLine (hB q p₁ hq) i inferInstance, ?_⟩
  have e : (i ≫ pullback.fst p₁ q) ≫ p₁ = (i ≫ pullback.snd p₁ q) ≫ q := by
    rw [Category.assoc, pullback.condition, Category.assoc]
  rw [e]
  exact IT_of_iterLine hq _ inferInstance

end LateralTheory.E.ChowLCut

end
