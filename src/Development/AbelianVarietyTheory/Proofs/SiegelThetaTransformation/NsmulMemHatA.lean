import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.VacBase

theorem exists_reps {G H : Type} [AddCommGroup G] [AddCommGroup H] (A B : AddSubgroup G) (A₀ : AddSubgroup H)
    (hfg : A₀.FG) (φ : H →+ G) (hφ : ∀ y ∈ A₀, φ y ∈ A) (hs : ∀ u ∈ A, ∃ y ∈ A₀, u - φ y ∈ B) (k : ℕ)
    (hN : ∀ u ∈ A, (2 * k + 1) • u ∈ B) :
    ∃ Ys : Finset G, (∀ y ∈ Ys, ∃ u ∈ A, y = 2 • u) ∧ ∀ u ∈ A, ∃! y, y ∈ Ys ∧ u - y ∈ B := by
  haveI : AddGroup.FG A₀ := (AddGroup.fg_iff_addSubgroup_fg A₀).2 hfg
  let φ' : A₀ →+ A := (φ.comp A₀.subtype).codRestrict A fun y => hφ y y.2
  have hq : ∀ a b : A, (a : A ⧸ B.addSubgroupOf A) = b ↔ (a : G) - b ∈ B := fun a b => by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]; rfl
  have hsurj : Function.Surjective ((QuotientAddGroup.mk' (B.addSubgroupOf A)).comp φ') := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y, hy, h⟩ := hs u u.2
    exact ⟨⟨y, hy⟩, ((hq _ _).2 h).symm⟩
  haveI : AddGroup.FG (A ⧸ B.addSubgroupOf A) := AddGroup.fg_of_surjective hsurj
  haveI : Finite (A ⧸ B.addSubgroupOf A) := by
    refine AddCommGroup.finite_of_fg_torsion _ fun q => ?_
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2 * k + 1, Nat.succ_pos _, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hN u u.2
  haveI := Fintype.ofFinite (A ⧸ B.addSubgroupOf A)
  let r : A ⧸ B.addSubgroupOf A → G := fun c => 2 • ((k + 1) • (c.out : G))
  have hr : ∀ (u : A) c, (u : G) - r c ∈ B ↔ (u : A ⧸ B.addSubgroupOf A) = c := fun u c => by
    have e : (u : G) - r c = ((u : G) - c.out) - (2 * k + 1) • (c.out : G) := by
      simp only [r]; module
    rw [e, sub_eq_add_neg, B.add_mem_cancel_right (B.neg_mem (hN _ c.out.2)), ← hq, QuotientAddGroup.out_eq']
  refine ⟨Finset.univ.image r, fun y hy => ?_, fun u hu => ?_⟩
  · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨_, A.nsmul_mem c.out.2 _, rfl⟩
  · refine ⟨r (⟨u, hu⟩ : A), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (hr ⟨u, hu⟩ _).2 rfl⟩, ?_⟩
    rintro y ⟨hy, h⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
    rw [(hr ⟨u, hu⟩ c).1 h]


theorem nsmul_mem_hatA {D : D7} (S T : HSp D) (Λ : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank) (N : ℕ)
    (h : ∀ v ∈ L, N • v ∈ L') : ∀ u ∈ hatA S T (tens Λ L), N • u ∈ hatA S T (tens Λ L') := by
  have h1 : tens Λ L ≤ (tens Λ L').comap (nsmulAddMonoidHom N) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    exact AddSubgroup.subset_closure ⟨v, hv, N • u, h u hu, (map_nsmul (LatTens.vmv v) N u).symm⟩
  have h2 : hatA S T (tens Λ L) ≤ (hatA S T (tens Λ L')).comap (nsmulAddMonoidHom N) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, y, hy, rfl⟩
    exact AddSubgroup.subset_closure ⟨α, hα, N • y, h1 hy, (map_nsmul (LatTens.gen S T α) N y).symm⟩
  exact fun u hu => h2 hu


end GlobalTheory.Ker.VacBase
