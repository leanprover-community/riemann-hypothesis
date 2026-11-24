module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.AICAcycPf

theorem acyc_of_iso (q : ℕ) {X Y : Scheme.{0}} (e : X ≅ Y) (h : Acyc q (sch.obj Y)) : Acyc q (sch.obj X) := by
  intro n i hn
  have := h n i hn
  constructor
  intro a b
  have key : ∀ a : Ht q (sch.obj X) n i,
      a = pull _ (sch.map e.hom) _ n (pull _ (sch.map e.inv) _ n a) := by
    intro a
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key a, key b, Subsingleton.elim (pull _ (sch.map e.inv) _ n a) (pull _ (sch.map e.inv) _ n b)]

theorem aff (hB5 : B5) (q : ℕ) (Z : Scheme.{0}) [IsAffine Z] (hZ : AICSch Z) (hq : IsUnit (q : Γ(Z, ⊤))) :
    Acyc q (sch.obj Z) := by
  have : IsIntegral Z := hZ.1
  have hA : AIC Γ(Z, ⊤) := hZ.2 ⊤ (isAffineOpen_top Z) ⟨Nonempty.some inferInstance, by simp⟩
  have h5 := hB5 q Γ(Z, ⊤) hA hq
  exact acyc_of_iso q Z.isoSpec h5

def Step : Prop := Hyp → MV → HZero → ∀ (q : ℕ) {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
  [IsOpenImmersion g], Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
  Acyc q (sch.obj U) → Acyc q (sch.obj V) → (Nonempty ↥(pullback f g : Scheme.{0}) → Acyc q (sch.obj (pullback f g))) → Acyc q (sch.obj X)

def Cov : Prop := ∀ (q : ℕ) (P : Scheme.{0} → Prop), (∀ {X Y : Scheme.{0}}, (X ≅ Y) → P Y → P X) →
  (∀ Z : Scheme.{0}, IsAffine Z → AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z) →
  (∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
    Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
    P U → P V → (Nonempty ↥(pullback f g : Scheme.{0}) → P (pullback f g)) → P X) →
  ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z], AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z

theorem AICAcyc_of (hZ : HZero) (hMV : MV) (hStep : Step) (hCov : Cov) : AICAcyc := by
  intro hyp q Z _ _ hZs hq
  refine hCov q (fun W => Acyc q (sch.obj W)) ?_ ?_ ?_ Z hZs hq
  · intro X Y e h
    exact acyc_of_iso q e h
  · intro W hA hW hWq
    exact aff hyp.b5 q W hW hWq
  · intro U V X f g _ _ hc hX hU hV hq' hPU hPV hPW
    exact hStep hyp hMV hZ q f g hc hX hU hV hq' hPU hPV hPW

end LateralTheory.E.AICAcycPf
