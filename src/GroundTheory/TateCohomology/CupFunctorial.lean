module

public import GroundTheory.TateCohomology.CupProduct
public import Mathlib.Tactic.Continuity
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Rep

namespace GroundTheory.GroupCoh

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem partialProd_comp {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {m : ℕ}
    (x : Fin m → M) (i : Fin (m + 1)) :
    Fin.partialProd (f ∘ x) i = f (Fin.partialProd x i) := by
  simp [Fin.partialProd, ← List.map_ofFn, ← List.map_take, map_list_prod]

variable (f : G →* H) {A₁ A₂ : Rep k H} {B₁ B₂ : Rep k G} {p q n : ℕ}

def resTensorHom (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) : res f (A₁ ⊗ A₂) ⟶ B₁ ⊗ B₂ :=
  ConcreteCategory.ofHom (C := Rep k G)
    { toLinearMap := TensorProduct.map φ₁.hom.toLinearMap φ₂.hom.toLinearMap
      isIntertwining' := fun g => TensorProduct.ext' fun a b => by
        change φ₁.hom (A₁.ρ (f g) a) ⊗ₜ[k] φ₂.hom (A₂.ρ (f g) b) =
          B₁.ρ g (φ₁.hom a) ⊗ₜ[k] B₂.ρ g (φ₂.hom b)
        rw [← Rep.hom_comm_apply φ₁, ← Rep.hom_comm_apply φ₂]
        rfl }

theorem resTensorHom_tmul (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (a : A₁) (b : A₂) :
    (resTensorHom f φ₁ φ₂).hom (a ⊗ₜ[k] b : (A₁ ⊗ A₂ : Rep k H)) = φ₁.hom a ⊗ₜ[k] φ₂.hom b :=
  rfl

theorem resTensorHom_cupCochain (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (x : (Fin p → H) → A₁) (y : (Fin q → H) → A₂) (g : Fin n → G) :
    (resTensorHom f φ₁ φ₂).hom (cupCochain h x y (f ∘ g)) =
      cupCochain h (fun v => φ₁.hom (x (f ∘ v))) (fun v => φ₂.hom (y (f ∘ v))) g := by
  rw [cupCochain_apply, resTensorHom_tmul, cupCochain_apply, partialProd_comp]
  exact congrArg _ (Rep.hom_comm_apply φ₂ _ _)

theorem map_π_apply' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B) (z : cocycles A n) :
    map f φ n (π A n z) = π B n (cocyclesMap f φ n z) := by
  change (π A n ≫ map f φ n).hom z = (cocyclesMap f φ n ≫ π B n).hom z
  rw [π_map]

theorem iCocycles_cocyclesMap' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B)
    (z : cocycles A n) :
    iCocycles B n (cocyclesMap f φ n z) = fun g => φ.hom (iCocycles A n z (f ∘ g)) := by
  change (cocyclesMap f φ n ≫ iCocycles B n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

theorem map_resTensorHom_cupH (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (a : groupCohomology A₁ p) (b : groupCohomology A₂ q) :
    map f (resTensorHom f φ₁ φ₂) n (cupH h a b) = cupH h (map f φ₁ p a) (map f φ₂ q b) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  have key : cocyclesMap (A := A₁ ⊗ A₂) f (resTensorHom f φ₁ φ₂) n (cupCocycles h z w) =
      cupCocycles h (cocyclesMap f φ₁ p z) (cocyclesMap f φ₂ q w) := by
    refine cocycles_ext ?_
    rw [iCocycles_cocyclesMap', iCocycles_cupCocycles, iCocycles_cupCocycles,
      iCocycles_cocyclesMap', iCocycles_cocyclesMap']
    funext g
    exact resTensorHom_cupCochain f φ₁ φ₂ h _ _ g
  rw [cupH_π, map_π_apply', map_π_apply', map_π_apply', cupH_π, key]

end GroundTheory.GroupCoh
