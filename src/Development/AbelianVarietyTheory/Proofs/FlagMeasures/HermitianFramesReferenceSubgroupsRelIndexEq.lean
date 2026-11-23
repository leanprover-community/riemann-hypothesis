module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConstStatement
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.RefVol

theorem relIndex_inf_of_le {G : Type*} [AddGroup G] (P A K : AddSubgroup G) (h : K ≤ P) :
    (P ⊓ A).relIndex K = A.relIndex K := by
  rw [← AddSubgroup.inf_relIndex_right (P ⊓ A) K, ← AddSubgroup.inf_relIndex_right A K]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨h hx.2, hx.1⟩, hx.2⟩⟩

theorem relIndex_prod {G H : Type*} [AddGroup G] [AddGroup H] (A A' : AddSubgroup G)
    (B B' : AddSubgroup H) :
    (A.prod B).relIndex (A'.prod B') = A.relIndex A' * B.relIndex B' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective _ (f := (AddSubgroup.prodEquiv A' B').toAddMonoidHom)
      (AddSubgroup.prodEquiv A' B').surjective]
  congr 1

theorem relIndex_inf_comap {G H : Type*} [AddGroup G] [AddGroup H] (φ : G →+ H) (P : AddSubgroup G)
    (A B : AddSubgroup H) :
    (P ⊓ A.comap φ).relIndex (P ⊓ B.comap φ) = (A ⊓ P.map φ).relIndex (B ⊓ P.map φ) := by
  rw [relIndex_inf_of_le _ _ _ inf_le_left, AddSubgroup.relIndex_comap, inf_comm A,
    relIndex_inf_of_le _ _ _ inf_le_right]
  congr 1
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨h2, x, h1, rfl⟩
  · rintro ⟨h2, x, h1, rfl⟩
    exact ⟨x, ⟨h1, h2⟩, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

noncomputable def sumDiv : S.V × S.V →+ S.V :=
  (algebraMap F E S.th⁻¹ • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom.comp
    (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

theorem sumDiv_apply (p : S.V × S.V) : sumDiv S p = algebraMap F E S.th⁻¹ • (p.1 + p.2) := rfl

theorem th_mul : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ (th_ne S), map_one]

theorem refB_eq (J : ℕ) (Λ : Submodule L.O S.V) :
    S.refB J Λ = ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
      Λ.toAddSubgroup.comap (sumDiv S) := by
  unfold Frames.refB
  congr 1
  ext p
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, sumDiv_apply]
  constructor
  · rintro ⟨y, hy, h⟩
    have h' : algebraMap F E S.th • y = p.1 + p.2 := h
    rw [← h', smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    change algebraMap F E S.th • (algebraMap F E S.th⁻¹ • (p.1 + p.2)) = p.1 + p.2
    rw [smul_smul, th_mul, one_smul]

theorem map_sumDiv (X X' : Submodule E S.V) :
    (X.toAddSubgroup.prod X'.toAddSubgroup).map (sumDiv S) = (X ⊔ X').toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup, sumDiv_apply]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.add_mem_sup h1 h2)
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    refine ⟨(algebraMap F E S.th • a, algebraMap F E S.th • b),
      ⟨X.smul_mem _ ha, X'.smul_mem _ hb⟩, ?_⟩
    rw [← smul_add, smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]

theorem refB_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refB J Λ).relIndex (S.refB J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup := by
  rw [refB_eq, refB_eq, relIndex_inf_comap, map_sumDiv]
  rfl

theorem refA_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refA J Λ).relIndex (S.refA J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup *
      (Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup := by
  unfold Frames.refA
  rw [relIndex_prod, relIndex_prod, AddSubgroup.relIndex_self, mul_one, refB_relIndex]
  rfl

end GlobalTheory.RefVol

theorem GlobalTheory.RefVol.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ h1 h2 Λ' h3 h4
  have a := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inl rfl)
  have b := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inr rfl)
  rw [GlobalTheory.RefVol.refA_relIndex, GlobalTheory.RefVol.refA_relIndex]
  exact ⟨by rw [a.1, b.1], mul_ne_zero a.2.1 b.2.1⟩
