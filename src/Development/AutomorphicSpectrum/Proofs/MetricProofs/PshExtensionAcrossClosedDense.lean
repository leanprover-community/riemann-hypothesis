module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
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
public import Mathlib.Geometry.Manifold.IsManifold.Basic
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.AnForm

theorem isPsh_of_dense_compl : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (Q Q' : LocPot X), IsClosed B → Dense Bᶜ → (∀ x, Q'.U x = Q.U x) → (∀ x, A.SmoothOn (Q'.U x) (Q'.φ x)) → (∀ x, ∀ y ∈ Q.U x, y ∉ B → Q'.φ x y = Q.φ x y) → IsPshOn A Bᶜ Q → IsPsh A Q' := by
  intro e X _ A B Q Q' hB hD hU hS hE hP x j y hy w
  by_contra hneg
  have hneg' : levi (Q'.φ x ∘ (A.chart j).symm) y w < 0 := not_le.mp hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (Q'.isOpen_U x)
  have hf : ContDiffOn ℝ 2 (Q'.φ x ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (hS x j).of_le ENat.LEInfty.out
  have hc := continuousOn_levi hO hf
  have hc' : ContinuousOn (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    hc.comp (f := fun y' => (y', w)) (by fun_prop) (fun y' hy' => ⟨hy', Set.mem_univ _⟩)
  have hV := hc'.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))
  set V := ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) ∩
    (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w) ⁻¹' Set.Iio 0 with hVdef
  have hVt : V ⊆ (A.chart j).target := fun z hz => hz.1.1
  have hVi : IsOpen ((A.chart j).symm '' V) :=
    (A.chart j).symm.isOpen_image_of_subset_source hV hVt
  have hne : ((A.chart j).symm '' V).Nonempty := ⟨_, y, ⟨hy, hneg'⟩, rfl⟩
  obtain ⟨z, ⟨y', hy'V, rfl⟩, hzB⟩ := hD.inter_open_nonempty _ hVi hne
  have hW : IsOpen (V ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
    have h1 := (A.chart j).isOpen_inter_preimage_symm hB.isOpen_compl
    have : V ∩ (A.chart j).symm ⁻¹' Bᶜ =
        V ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
      ext u
      exact ⟨fun h => ⟨h.1, hVt h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [this]
    exact hV.inter h1
  have hev : (Q'.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y'] (Q.φ x ∘ (A.chart j).symm) := by
    filter_upwards [hW.mem_nhds ⟨hy'V, hzB⟩] with u hu
    have huU : (A.chart j).symm u ∈ Q.U x := hU x ▸ hu.1.1.2
    exact hE x _ huU hu.2
  have h0 := hP x j y' ⟨hy'V.1.1, (hU x ▸ hy'V.1.2 : (A.chart j).symm y' ∈ Q.U x), hzB⟩ w
  rw [← levi_congr hev w] at h0
  exact absurd h0 (not_le.mpr hy'V.2)

end GlobalTheory.CompanionTheory.AnForm
