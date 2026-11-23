module

public import GroundTheory.TateCohomology.CupTateShift
public import GroundTheory.TateCohomology.TateLow
public import GroundTheory.TateCohomology.CupTate
import GroundTheory.TateCohomology.DimensionShift
import GroundTheory.TateCohomology.InducedNorm
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

set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Unitors

variable (E : ShortComplex (Rep.{u} k G))

noncomputable def leftUnitorSCIso : E.map (tensorLeft (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (λ_ E.X₁) (λ_ E.X₂) (λ_ E.X₃) (leftUnitor_naturality E.f).symm
    (leftUnitor_naturality E.g).symm

noncomputable def rightUnitorSCIso : E.map (tensorRight (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (ρ_ E.X₁) (ρ_ E.X₂) (ρ_ E.X₃) (rightUnitor_naturality E.f).symm
    (rightUnitor_naturality E.g).symm

variable {E}

theorem shortExact_tensorLeft_unit (hE : E.ShortExact) :
    (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact :=
  ShortComplex.shortExact_of_iso (leftUnitorSCIso E).symm hE

theorem shortExact_tensorRight_unit (hE : E.ShortExact) :
    (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact :=
  ShortComplex.shortExact_of_iso (rightUnitorSCIso E).symm hE

variable [Fintype G]

theorem δ_leftUnitor_apply (hE : E.ShortExact)
    (hE' : (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (𝟙_ (Rep.{u} k G) ⊗ E.X₃) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (λ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (λ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) :=
  congr(($(TateCohomology.δ_naturality hE' hE (leftUnitorSCIso E).hom i)).hom x).symm

theorem δ_rightUnitor_apply (hE : E.ShortExact)
    (hE' : (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (E.X₃ ⊗ 𝟙_ (Rep.{u} k G)) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (ρ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (ρ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) :=
  congr(($(TateCohomology.δ_naturality hE' hE (rightUnitorSCIso E).hom i)).hom x).symm

end Unitors

variable [Fintype G]


variable (k G) in
noncomputable def tateOne : tateCohomology (𝟙_ (Rep.{u} k G)) 0 :=
  ((tateCohomologyZeroIso k G).app (𝟙_ (Rep.{u} k G))).inv.hom
    (Submodule.Quotient.mk ⟨(1 : k), fun _ => rfl⟩)



theorem leftUnitor_tateCup_tateOne_zero (B : Rep.{u} k G) (b : tateCohomology B 0) :
    ((tateCohomologyFunctor 0).map (λ_ B).hom).hom
      (tateCup 0 0 (𝟙_ (Rep.{u} k G)) B 0 (zero_add 0) (tateOne k G) b) = b := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (((tateCohomologyZeroIso k G).app B).hom.hom b)
  have hb : b = ((tateCohomologyZeroIso k G).app B).inv.hom (Submodule.Quotient.mk y) := by
    rw [hy]
    exact (((tateCohomologyZeroIso k G).app B).hom_inv_id_apply b).symm
  subst hb
  have h0 := tateCup_zero_zero (𝟙_ (Rep.{u} k G)) B ⟨(1 : k), fun _ => rfl⟩ y
  refine (congrArg (((tateCohomologyFunctor 0).map (λ_ B).hom).hom) h0).trans ?_
  have hn := congr(($((tateCohomologyZeroIso k G).inv.naturality (λ_ B).hom)).hom
    (Submodule.Quotient.mk (tensorInvariants (⟨(1 : k), fun _ => rfl⟩ :
      (𝟙_ (Rep.{u} k G)).ρ.invariants) y)))
  refine hn.symm.trans ?_
  change ((tateCohomologyZeroIso k G).inv.app B).hom (Submodule.Quotient.mk _) = _
  congr 2
  apply Subtype.ext
  change (λ_ B).hom.hom ((1 : k) ⊗ₜ[k] (y : B)) = y
  rw [leftUnitor_hom_tmul, one_smul]

theorem leftUnitor_tateCup_tateOne_down (q q' : ℤ) (hq : q + 1 = q')
    (h : ∀ (B : Rep.{u} k G) (b : tateCohomology B q'),
      ((tateCohomologyFunctor q').map (λ_ B).hom).hom
        (tateCup 0 q' (𝟙_ (Rep.{u} k G)) B q' (zero_add _) (tateOne k G) b) = b)
    (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  subst hq
  have hE := augSES_shortExact B
  have hAE := augSES_tensorLeft_shortExact (𝟙_ (Rep.{u} k G)) B
  have hiso : IsIso (TateCohomology.δ hE q) :=
    isIso_δ_of_tateAcyclic hE (tateAcyclic_leftRegular_tensor B) q
  apply moduleIso_hom_injective (@asIso _ _ _ _ _ hiso)
  refine (δ_leftUnitor_apply hE hAE q _).trans ?_
  have hr := tateCup_δ_right hE (𝟙_ (Rep.{u} k G)) hAE 0 q q (zero_add q) (tateOne k G) b
  rw [Int.negOnePow_zero, one_smul] at hr
  refine (congrArg (((tateCohomologyFunctor (q + 1)).map (λ_ _).hom).hom) hr).trans ?_
  exact h _ _

theorem leftUnitor_tateCup_tateOne_up (q q' : ℤ) (hq : q + 1 = q')
    (h : ∀ (B : Rep.{u} k G) (b : tateCohomology B q),
      ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b)
    (B : Rep.{u} k G) (b : tateCohomology B q') :
    ((tateCohomologyFunctor q').map (λ_ B).hom).hom
        (tateCup 0 q' (𝟙_ (Rep.{u} k G)) B q' (zero_add _) (tateOne k G) b) = b := by
  subst hq
  have hE := coindSES_shortExact B
  have hAE := shortExact_tensorLeft_unit hE
  have hiso : IsIso (TateCohomology.δ hE q) := isIso_δ_coindSES B q
  obtain ⟨c, rfl⟩ : ∃ c, (TateCohomology.δ hE q).hom c = b :=
    ⟨(@asIso _ _ _ _ _ hiso).inv.hom b, (@asIso _ _ _ _ _ hiso).inv_hom_id_apply b⟩
  have hr := tateCup_δ_right hE (𝟙_ (Rep.{u} k G)) hAE 0 q q (zero_add q) (tateOne k G) c
  rw [Int.negOnePow_zero, one_smul] at hr
  refine (congrArg (((tateCohomologyFunctor (q + 1)).map (λ_ _).hom).hom) hr.symm).trans ?_
  refine (δ_leftUnitor_apply hE hAE q _).symm.trans ?_
  exact congrArg (TateCohomology.δ hE q).hom (h _ _)

theorem leftUnitor_tateCup_tateOne (q : ℤ) (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  induction q using Int.induction_on generalizing B with
  | zero => exact leftUnitor_tateCup_tateOne_zero B b
  | succ i ih => exact leftUnitor_tateCup_tateOne_up (i : ℤ) _ rfl ih B b
  | pred i ih => exact leftUnitor_tateCup_tateOne_down _ (-(i : ℤ)) (by ring) ih B b

end GroundTheory.GroupCoh
