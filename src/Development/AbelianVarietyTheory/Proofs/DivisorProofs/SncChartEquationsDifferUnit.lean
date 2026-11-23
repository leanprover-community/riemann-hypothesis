module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

theorem sncChart_germ_eqn_unit : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Sp R) {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ (C C' : SncChart g n L σ) (y : Y) (hy : y ∈ C.U) (hy' : y ∈ C'.U) (c : Fin s), ∃ v : (Y.presheaf.stalk y)ˣ, (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) = v * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t) := by
  intro R _ Y g n s L σ hL C C' y hy hy' c
  have hyi : y ∈ (L c).U (C.c c) := C.le c hy
  have hyj : y ∈ (L c).U (C'.c c) := C'.le c hy'
  have hyij : y ∈ (L c).U (C.c c) ⊓ (L c).U (C'.c c) := ⟨hyi, hyj⟩
  have e1 := congrArg (Y.presheaf.germ C.U y hy).hom (C.eq c)
  have e2 := congrArg (Y.presheaf.germ C'.U y hy').hom (C'.eq c)
  have e3 := congrArg (Y.presheaf.germ _ y hyij).hom ((σ c).2 (C.c c) (C'.c c))
  simp only [resG, map_mul, TopCat.Presheaf.germ_res_apply] at e1 e2 e3
  let w0 := Units.map (Y.presheaf.germ C.U y hy).hom.toMonoidHom (C.u c)
  let w1 := Units.map (Y.presheaf.germ C'.U y hy').hom.toMonoidHom (C'.u c)
  let wg := Units.map (Y.presheaf.germ _ y hyij).hom.toMonoidHom ((L c).g (C.c c) (C'.c c))
  refine ⟨w0⁻¹ * wg * w1, ?_⟩
  have key : (w0 : Y.presheaf.stalk y) * (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) =
      (wg : Y.presheaf.stalk y) * ((w1 : Y.presheaf.stalk y) * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t)) := by
    exact e1.symm.trans (e3.trans (congrArg (fun z => _ * z) e2))
  calc (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t)
      = ((w0⁻¹ : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) * ((w0 : Y.presheaf.stalk y) * (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [key]; simp only [Units.val_mul, mul_assoc]

end GlobalTheory.LogPair
