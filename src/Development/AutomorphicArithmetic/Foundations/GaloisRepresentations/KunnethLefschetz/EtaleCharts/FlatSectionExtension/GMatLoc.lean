module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatLocal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaDisj
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

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatLoc :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)) (α β : B.ι) (a₁ : V ⟶ (oW B α : Scheme.{0})) (b₁ : V ⟶ (oW B β : Scheme.{0})), a = a₁ ≫ wI B α → b = b₁ ≫ wI B β → GMat B a b M → LocMat B α β (a ≫ cP B) M := by
  intro K _ W Z Y q i π D d B V a b M α β a₁ b₁ ha hb hG
  refine UpperTheory.Gal.KunnethLefschetz.G.PX.locMatLocal B α β (a ≫ cP B) M fun x => ?_
  obtain ⟨U, α', β', a', b', hx, h1, h2, hL⟩ := hG x
  have e1 : α' = α := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun γ : B.ι => (oW B γ : Scheme.{0})) a' (U.ι ≫ a₁) (⟨x, hx⟩ : U) ?_
    have h : a' ≫ wI B α' = (U.ι ≫ a₁) ≫ wI B α := by
      rw [← h1, ha, Category.assoc]
    exact h
  have e2 : β' = β := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun γ : B.ι => (oW B γ : Scheme.{0})) b' (U.ι ≫ b₁) (⟨x, hx⟩ : U) ?_
    have h : b' ≫ wI B β' = (U.ι ≫ b₁) ≫ wI B β := by
      rw [← h2, hb, Category.assoc]
    exact h
  subst e1 e2
  exact ⟨U, hx, hL⟩
