module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.LineUniv

theorem exists_line : ∀ {C : Type u} [Category.{v} C] (U : UF C) (P : ∀ ⦃T T' : C⦄, (T ⟶ T') → (T' ⟶ T') → Prop), (∀ T : C, ∃ (T₁ : C) (i : T ⟶ T₁) (η : U.U T₁), (∀ (T' : C) (φ : T ⟶ T') (a : U.U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ U.map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → U.map g η = U.q _ * η → P i g) → ∃ L : Line (𝟭 C) U, ∀ T, P (L.i.app T) (L.γ.app T) := by
  intro C _ U P h
  choose T₁ i η hu hP using h
  have hm : ∀ (T T' : C) (φ : T ⟶ T'), ∃ ψ : T₁ T ⟶ T₁ T', i T ≫ ψ = φ ≫ i T' ∧ U.map ψ (η T) = η T' :=
    fun T T' φ => (hu T _ (φ ≫ i T') (η T')).exists
  choose m hm1 hm2 using hm
  have hg : ∀ T, ∃ g : T₁ T ⟶ T₁ T, i T ≫ g = i T ∧ U.map g (η T) = U.q _ * η T :=
    fun T => (hu T _ (i T) _).exists
  choose g hg1 hg2 using hg
  have uniq : ∀ (T T' : C) (φ : T ⟶ T') (a : U.U T') (ψ ψ' : T₁ T ⟶ T'), i T ≫ ψ = φ → U.map ψ (η T) = a →
      i T ≫ ψ' = φ → U.map ψ' (η T) = a → ψ = ψ' :=
    fun T T' φ a ψ ψ' h1 h2 h3 h4 => (hu T T' φ a).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  let Ξ : C ⥤ C :=
    { obj := T₁
      map := fun {T T'} φ => m T T' φ
      map_id := fun T => uniq T _ (i T) (η T) _ _ (by rw [hm1, Category.id_comp]) (hm2 _ _ _)
        (Category.comp_id _) (U.map_id _ _)
      map_comp := fun {T T' T''} φ ψ => uniq T _ (φ ≫ ψ ≫ i T'') (η T'') _ _
        (by rw [hm1, Category.assoc]) (hm2 _ _ _)
        (by rw [← Category.assoc, hm1, Category.assoc, hm1])
        (by rw [U.map_comp, hm2, hm2]) }
  let iN : 𝟭 C ⟶ Ξ :=
    { app := i
      naturality := fun {T T'} φ => (hm1 T T' φ).symm }
  let γN : Ξ ⟶ Ξ :=
    { app := g
      naturality := fun {T T'} φ => uniq T _ (φ ≫ i T') (U.q _ * η T') _ _
        (by
          change i T ≫ m T T' φ ≫ g T' = _
          rw [← Category.assoc, hm1, Category.assoc, hg1])
        (by
          change U.map (m T T' φ ≫ g T') (η T) = _
          rw [U.map_comp, hm2, hg2])
        (by
          change i T ≫ g T ≫ m T T' φ = _
          rw [← Category.assoc, hg1, hm1])
        (by
          change U.map (g T ≫ m T T' φ) (η T) = _
          rw [U.map_comp, hg2, map_mul, hm2, U.map_q]) }
  refine ⟨{ Ξ := Ξ, i := iN, η := η, map_η := fun {T T'} φ => hm2 T T' φ, γ := γN, iγ := ?_, γη := hg2, univ := ?_ }, ?_⟩
  · ext T
    exact hg1 T
  · intro T t φ a
    exact hu T t φ a
  · intro T
    exact hP T (g T) (hg1 T) (hg2 T)

end GlobalTheory.CompanionTheory.LineUniv
