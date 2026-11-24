module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.JetSer

theorem valSer_germ_fnVal {A : Type} [CommRing A] {Y : Scheme.{0}} (r : Spec (CommRingCat.of A) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Spec (CommRingCat.of A)) (f : Γ(Y, U)) :
    ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (fnVal r U f)) = gs r z U f := by
  have hz : r z ∈ U := h (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial)
  rw [gs_eq r z U hz, fnVal, dite_eq_left h]
  have e : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) = a :=
    fun a => (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id_apply a
  rw [e]
  exact TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of A)).presheaf (homOfLE h) z trivial _

theorem valSer : ValSerSt := by
  intro A _ X L hL j z Ψ _ hΨ
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Ψ) (fun ψ => ψ.1) (fun _ => j) (fun _ _ _ => rfl)
    (fun ψ => hΨ ψ.1 ψ.2 (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial))
  refine ⟨J, hJ, fun Y K _ φ ε t r hr => ?_⟩
  have hU : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j) := fun y hy => Set.mem_iInter.2 fun k => hΨ _ (hr k) hy
  rw [val_of t r z J (fun _ => j) (fun k => e ⟨_, hr k⟩)]
  exact (gs_unit r z _ (hU (show z ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial)) _).symm.trans
    (valSer_germ_fnVal r _ hU z _).symm

end GlobalTheory.JetSer
