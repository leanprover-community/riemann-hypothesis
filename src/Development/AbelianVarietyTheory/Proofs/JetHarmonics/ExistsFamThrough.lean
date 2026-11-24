module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExp
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LinOfSval
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalOfPointwise
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitBallBox

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem box_secScal {S : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    {f' : ∀ α : D'.X, D'.SecB k α} {f : Fin j → ∀ α : D.X, D.SecB k α} (hf : IsBoxFamB pD k f' f) (α' : D'.X)
    (h : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F (pD.xe α' i)) (DegPre.famε k) ((s i).s (pD.xe α' i))
      (D.famφB (pD.xe α' i)) (DegPre.famε k) (f i (pD.xe α' i)) (DegPre.prB D F).left 1) :
    GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' F α') (DegPre.famε k) (S.s α')
      (D'.famφB α') (DegPre.famε k) (f' α') (DegPre.prB D' F).left 1 := by
  obtain ⟨hφ, H⟩ := hS α'
  obtain ⟨hψ, H'⟩ := hf α'
  have e₄ : ∀ i, (DegPre.prB D' F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D F).left := fun i => by
    rw [← Over.comp_left, ← Over.comp_left]; congr 1; exact (whiskerLeft_snd _ _).symm
  exact BoxFamScalar.secScal_box D.P.isLB D'.P.isLB pD.w (GC.famφ_eq D' F α') e₄
    (S.s α') (fun i => (s i).s (pD.xe α' i)) (f' α') (fun i => f i (pD.xe α' i))
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hφ (S.s α') (fun i => (s i).s (pD.xe α' i)) _ H (𝟙 _) y hJ hJ')
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hψ (f' α') (fun i => f i (pD.xe α' i)) _ H' _ y hJ hJ')
    (fun _ => 1) 1 (fun y => by simp only [NuBox.gs_one, Finset.prod_const_one]) h

end Fam


end GlobalTheory.UnitBallBox
