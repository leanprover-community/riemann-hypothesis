module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}
  {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp (D.OEp p)} {s₂ : S₂ ⟶ Sp (D.OEp p)} {s₃ : S₃ ⟶ Sp (D.OEp p)}
  {o₁ : Obj D p N s₁} {o₂ : Obj D p N s₂} {o₃ : Obj D p N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}

def ObjMap.comp (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  act a := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.PP.isLB (pull_isLB o₂.PP.isLB m₁.φ) (pull_isLB o₃.PP.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o₂.PP.L m₁.φ)
      (chartPullSame o₃.PP.L (fun _ : PUnit => m₁.φ ≫ m₂.φ) (fun _ => m₂.φ) (fun _ => 1) m₁.φ (fun _ => rfl))
      m₂.pol)
  eta a := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem objMap_comp : ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (D : GlobalTheory.UPel.Datum F) (p N : ℕ)
    (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp (D.OEp p)) (s₂ : S₂ ⟶ Sp (D.OEp p)) (s₃ : S₃ ⟶ Sp (D.OEp p))
    (o₁ : GlobalTheory.UPel.Obj D p N s₁) (o₂ : GlobalTheory.UPel.Obj D p N s₂) (o₃ : GlobalTheory.UPel.Obj D p N s₃) (f : S₁ ⟶ S₂)
    (g : S₂ ⟶ S₃), GlobalTheory.UPel.ObjMap o₁ o₂ f → GlobalTheory.UPel.ObjMap o₂ o₃ g → Nonempty (GlobalTheory.UPel.ObjMap o₁ o₃ (f ≫ g)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m₁ m₂ => ⟨m₁.comp m₂⟩

end GlobalTheory.UPel
