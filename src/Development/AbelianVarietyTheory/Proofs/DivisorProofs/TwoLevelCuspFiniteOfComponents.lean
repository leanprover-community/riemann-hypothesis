module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

namespace GlobalTheory.CompFin

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [NumberField E] [IsCMField E] in
theorem castFrame_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ' r) :
    castFrame h (castFrame h.symm x) = x := rfl

theorem castFrame_mem_GG (X : Data E r) {Ψ : Finset (E →+* ℂ)} (h : X.Ψ = Ψ) (x : Frame X.Ψ r) :
    castFrame h x ∈ GG Ψ X.Gm X.p0 ↔ x ∈ X.dom := by
  subst h
  rfl

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem castFrame_mem_dom (c : C) (x : Frame (M.comp c).Ψ r) :
    castFrame (M.comp_Ψ c) x ∈ M.dom ↔ x ∈ (M.comp c).dom := by
  have := castFrame_mem_GG (M.comp c).toData (M.comp_Ψ c) x
  rw [M.comp_Gm c, M.comp_basePoint c] at this
  exact this

def toComp (c : C) : (C → M.dom → ℂ) →ₗ[ℂ] ((M.comp c).dom → ℂ) where
  toFun v x := v c ⟨castFrame (M.comp_Ψ c) x.1, (castFrame_mem_dom M c x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cusp_le_comap (ka : Wt M.Ψ r) (c : C) :
    M.cusp ka ≤ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) ''
      (M.comp c).SS (castWt (M.comp_Ψ c) ka))).comap (toComp M c) := by
  unfold TwoLevels.cusp
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  exact Submodule.subset_span ⟨_, hF c, rfl⟩

theorem toComp_inj (v w : C → M.dom → ℂ) (h : ∀ c, toComp M c v = toComp M c w) : v = w := by
  funext c y
  have hy : castFrame (M.comp_Ψ c).symm y.1 ∈ (M.comp c).dom :=
    (castFrame_mem_dom M c _).1 (by rw [castFrame_castFrame]; exact y.2)
  have := congrFun (h c) ⟨_, hy⟩
  exact this

end

end GlobalTheory.CompFin


open GlobalTheory.CompFin in
theorem GlobalTheory.cusp_finite_of_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r), (∀ c : C, FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka)))) → Module.Finite ℂ (M.cusp ka) := by
  intro E _ _ _ r U C _ _ _ M ka hfin
  let S : (c : C) → Submodule ℂ ((M.comp c).dom → ℂ) := fun c => Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ =>
    fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka))
  have : ∀ c, Module.Finite ℂ (S c) := hfin
  let Φ : M.cusp ka →ₗ[ℂ] (∀ c, S c) := LinearMap.pi fun c =>
    ((toComp M c).domRestrict (M.cusp ka)).codRestrict (S c) fun v => cusp_le_comap M ka c v.2
  have hΦ : Function.Injective Φ := by
    intro v w hvw
    apply Subtype.ext
    apply toComp_inj M
    intro c
    have := congrArg Subtype.val (congrFun hvw c)
    exact this
  exact Module.Finite.of_injective Φ hΦ
