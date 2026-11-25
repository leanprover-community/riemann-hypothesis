module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

variable {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

theorem functionFieldMap_comp_dominant (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] :
    functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) := by
  ext f
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := X.presheaf.stalk ((t ≫ s) (genericPoint Z))) f
  have key : ∀ c : X.presheaf.stalk ((t ≫ s) (genericPoint Z)),
      functionFieldMap (t ≫ s) (algebraMap _ X.functionField c) =
        functionFieldMap t (functionFieldMap s (algebraMap _ X.functionField c)) := by
    intro c
    have h1 := functionFieldMap_algebraMap (t ≫ s) (genericPoint Z) c
    have h2 := functionFieldMap_algebraMap s (t (genericPoint Z)) c
    have h3 := functionFieldMap_algebraMap t (genericPoint Z) (s.stalkMap (t (genericPoint Z)) c)
    refine h1.trans (Eq.trans ?_ ((congrArg (functionFieldMap t) h2).trans h3).symm)
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  simp only [map_div₀, RingHom.comp_apply, key]

theorem pullCart_comp (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] (D : CartierDiv X) :
    pullCart (t ≫ s) D = pullCart t (pullCart s D) :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨g, hg⟩ := D.exists_isEqn ((t ≫ s) z)
    refine ⟨_, isEqn_pullCart (t ≫ s) hg, ?_⟩
    have e : fnPull (t ≫ s) g = fnPull t (fnPull s g) :=
      Units.ext (RingHom.congr_fun (functionFieldMap_comp_dominant s t) g)
    rw [e]
    exact isEqn_pullCart t (isEqn_pullCart s hg)

theorem isDivOfForm_ratPull_comp {k : Type} [Field k] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s]
    (t : Z ⟶ Y) [IsDominant t] (n : ℕ) (η : RatForms p n) (K : CartierDiv Z) :
    IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔
      IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) := by
  have key : ∀ (q q' : Z ⟶ Sp k) (_ : q = q') (φ : X.functionField →+* Z.functionField)
      (h : φ.comp (Cartier.constFn p) = Cartier.constFn q) (h' : φ.comp (Cartier.constFn p) = Cartier.constFn q'),
      IsDivOfForm (p := q) K (TopForm.formMap n φ h η) ↔
        IsDivOfForm (p := q') K (TopForm.formMap n φ h' η) := by
    intro q q' e φ h h'
    subst e
    rfl
  have h' : (functionFieldMap (t ≫ s)).comp (Cartier.constFn p) = Cartier.constFn (t ≫ s ≫ p) := by
    rw [EtaleKlt.functionFieldMap_comp_constFn, Category.assoc]
  have e : EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η) =
      TopForm.formMap n (functionFieldMap (t ≫ s)) h' η :=
    formMap_formMap _ _ _ (functionFieldMap_comp_dominant s t).symm _ _ _ η
  rw [e]
  exact key _ _ (Category.assoc t s p) _ _ h'

theorem pull_comp : ∀ (k : Type) [Field k] (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t], functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) ∧ (∀ D : CartierDiv X, pullCart (t ≫ s) D = pullCart t (pullCart s D)) ∧ ∀ (n : ℕ) (η : RatForms p n) (K : CartierDiv Z), IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔ IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) :=
  fun _ _ _ _ _ _ _ _ p s _ t _ =>
    ⟨functionFieldMap_comp_dominant s t, pullCart_comp s t, isDivOfForm_ratPull_comp p s t⟩

end GlobalTheory.Discrepancy
