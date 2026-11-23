module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZRelLevs

theorem zrel_levs : ∀ (h h' M : ℕ) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' T : Scheme.{0}) (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g → ZRel e jl o κ c' w' actw' → (∀ a, g ≫ (z.lev (jl a) ≫ act e).left = g ≫ (z.lev (jl a)).left) ∧ ∀ a, g ≫ (z.lev a).left = g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
  intro h h' M O _ e jl n o κ S' T t z act g c' w' actw' hpb hz
  obtain ⟨φ, φ₂, hφ, -, -, hl, ha⟩ := hpb
  obtain ⟨inc, pr, -, -, hip, hpi, -, hc, hw⟩ := hz
  have key : ∀ b (oo : O), (w'.lev b ≫ actw' oo).left ≫ φ = g ≫ (z.lev b ≫ act oo).left := by
    intro b oo
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hl, Category.assoc]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← key, ← hl]
    congr 2
    rw [← hc, Category.assoc, ← hpi, ← Category.assoc inc, hip, Category.id_comp]
  · rw [← hl, hw a]
    have e1 : ((List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left ≫ φ =
        (pushHom hφ (𝟙_ (Over T)) (List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left := rfl
    rw [e1, map_list_prod, List.map_ofFn]
    have e2 : g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left =
        (toUnit (Over.mk ((𝟙_ (Over T)).hom ≫ g)) ≫
          (List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
      rw [Over.comp_left, Over.toUnit_left]
      rfl
    rw [e2, GlobalTheory.comp_list_prod_ofFn]
    congr 3
    funext k
    apply Over.OverMorphism.ext
    show (c'.lev (κ k a) ≫ inc ≫ actw' (o k)).left ≫ φ = _
    rw [← Category.assoc, hc, key]
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_hom]
    rfl

end GlobalTheory.ZRelLevs
