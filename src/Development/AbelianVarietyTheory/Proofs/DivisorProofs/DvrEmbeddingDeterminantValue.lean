import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLatticeBoundSecond
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionQuotientLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningImageLattice
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEmbeddingDeterminantProperty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrDeterminantProductOrders
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantOrder
import Formalism.LocalToGlobal.ProjectiveLattices.AvMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntRingHomExtOfIsHausdorff

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem injective_into_line_span_eq_smul_span (C : Type) [Field C] (O : Type) [CommRing O]
    [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup W] [Module C W] [Module O W] [IsScalarTower O C W] (ι : V →ₗ[C] W) (x : V)
    (y : W) (hι : Function.Injective ι) (hW : Module.finrank C W = 1) (hx : x ≠ 0)
    (hy : y ≠ 0) :
    ∃ lam : C, lam ≠ 0 ∧ ι x = lam • y ∧
      ι '' (Submodule.span O {x} : Set V) = (fun w => lam • w) '' (Submodule.span O {y} : Set W) := by
  obtain ⟨lam, hlam⟩ := (finrank_eq_one_iff_of_nonzero' y hy).mp hW (ι x)
  have hιx : ι x ≠ 0 := by
    intro h
    exact hx (hι (h.trans ι.map_zero.symm))
  have hl : lam ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hlam
    exact hιx hlam.symm
  have key : ∀ t : O, ι (t • x) = lam • (t • y) := by
    intro t
    rw [← algebraMap_smul C t x, ι.map_smul, ← hlam, ← algebraMap_smul C t y, smul_smul,
      smul_smul, mul_comm]
  refine ⟨lam, hl, hlam.symm, ?_⟩
  ext w
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
    exact ⟨t • y, ⟨t, rfl⟩, (key t).symm⟩
  · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
    exact ⟨t • x, ⟨t, rfl⟩, key t⟩

example : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] [AddCommGroup W] [Module C W] [Module O W] [IsScalarTower O C W] (ι : V →ₗ[C] W) (x : V) (y : W), Function.Injective ι → Module.finrank C W = 1 → x ≠ 0 → y ≠ 0 → ∃ lam : C, lam ≠ 0 ∧ ι x = lam • y ∧ ι '' (Submodule.span O {x} : Set V) = (fun w => lam • w) '' (Submodule.span O {y} : Set W) :=
  @injective_into_line_span_eq_smul_span

end GlobalTheory
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

theorem GlobalTheory.span_ιMulti_span_range_eq : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h N : ℕ) (g : Fin h → V), Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range g) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O (Set.range (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s))) := by
  intro C _ O _ _ V _ _ _ _ h N g
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨x, hx, rfl⟩
    have hc : ∀ i, ∃ c : Fin h → O, ∑ j, c j • g j = x i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun O).1 (hx i)
    choose c hc using hc
    have hx' : x = fun i => ∑ j, (algebraMap O C (c i j)) • g j := by
      funext i; rw [← hc i]; simp [algebraMap_smul]
    rw [hx']
    show (exteriorPower.ιMulti C N).toMultilinearMap (fun i => ∑ j, (algebraMap O C (c i j)) • g j) ∈ _
    rw [MultilinearMap.map_sum]
    refine Submodule.sum_mem _ (fun s _ => ?_)
    rw [MultilinearMap.map_smul_univ, ← map_prod, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · apply Submodule.span_mono
    rintro w ⟨s, rfl⟩
    exact ⟨g ∘ s, fun i => Submodule.subset_span ⟨s i, rfl⟩, rfl⟩
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPower_span_of_lattice : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h N : ℕ) (g : Fin h → V), Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range g) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O (Set.range (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s))) := by
  atlas_forward_decl GlobalTheory.span_ιMulti_span_range_eq
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem topWedge_line_and_nonzero : ∀ (C : Type) [Field C] (V : Type) [AddCommGroup V] [Module C V] (h N : ℕ) (g : Fin h → V), Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → Module.finrank C (⋀[C]^N V) = 1 ∧ ∃ s : Fin N → Fin h, exteriorPower.ιMulti C N (g ∘ s) ≠ 0 := by
  intro C _ V _ _ h N g hspan hN
  haveI : Module.Finite C V := ⟨by rw [← hspan]; exact Submodule.fg_span (Set.finite_range g)⟩
  have h1 : Module.finrank C (⋀[C]^N V) = 1 := by
    rw [exteriorPower.finrank_eq, hN, Nat.choose_self]
  refine ⟨h1, ?_⟩
  by_contra hcon
  push_neg at hcon
  have htop := exteriorPower.ιMulti_span_of_span C N V hspan
  have hle : Submodule.span C (exteriorPower.ιMulti C N '' {a | Set.range a ⊆ Set.range g}) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro - ⟨a, ha, rfl⟩
    have hmem : ∀ i, ∃ j, g j = a i := fun i => ha ⟨i, rfl⟩
    choose s hs using hmem
    have : a = g ∘ s := funext fun i => (hs i).symm
    rw [this, hcon s]
    simp
  rw [htop, le_bot_iff] at hle
  have : Subsingleton (⋀[C]^N V) := subsingleton_of_forall_eq 0 fun x => by
    have hx : x ∈ (⊤ : Submodule C (⋀[C]^N V)) := trivial
    rw [hle] at hx
    simpa using hx
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact absurd h1 (by norm_num)

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPower_top_finrank_one : ∀ (C : Type) [Field C] (V : Type) [AddCommGroup V] [Module C V] (h N : ℕ) (g : Fin h → V), Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → Module.finrank C (⋀[C]^N V) = 1 ∧ ∃ s : Fin N → Fin h, exteriorPower.ιMulti C N (g ∘ s) ≠ 0 := by
  atlas_forward_decl GlobalTheory.topWedge_line_and_nonzero
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem finGen_line_span_principal (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    (I : Type) [Finite I] (u : I → V) (hv : v.Integers O) (h1 : Module.finrank C V = 1)
    (hu : ∃ i, u i ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ Submodule.span O (Set.range u) = Submodule.span O {w} := by
  obtain ⟨e, -, he⟩ := finrank_eq_one_iff'.mp h1
  choose c hc using fun i => he (u i)
  obtain ⟨j, hj⟩ := hu
  haveI : Nonempty I := ⟨j⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => v (c i))
  have hcj : c j ≠ 0 := by
    rintro h; apply hj; rw [← hc j, h, zero_smul]
  have hc0 : c i0 ≠ 0 := by
    intro h
    have := hi0 j
    rw [h, map_zero] at this
    exact hcj ((Valuation.zero_iff v).mp (le_antisymm this zero_le'))
  have key : ∀ i, ∃ t : O, u i = t • u i0 := by
    intro i
    have hle : v (c i / c i0) ≤ 1 := by
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff v).mpr hc0)]
      exact hi0 i
    obtain ⟨t, ht⟩ := hv.exists_of_le_one hle
    refine ⟨t, ?_⟩
    rw [← algebraMap_smul C t (u i0), ht, ← hc i, ← hc i0, smul_smul, div_mul_cancel₀ _ hc0]
  refine ⟨u i0, ?_, ?_⟩
  · rw [← hc i0]; exact smul_ne_zero hc0 (by rintro rfl; apply hj; rw [← hc j, smul_zero])
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨t, ht⟩ := key i
      rw [ht]; exact Submodule.smul_mem _ t (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨i0, rfl⟩

theorem finGen_line_span_principal_target : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (I : Type) [Finite I] (u : I → V), v.Integers O → Module.finrank C V = 1 → (∃ i, u i ≠ 0) → ∃ w : V, w ≠ 0 ∧ Submodule.span O (Set.range u) = Submodule.span O {w} :=
  fun C _ v O _ _ V _ _ _ _ I _ u hv h1 hu => finGen_line_span_principal C v O V I u hv h1 hu
end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_lattice_span_singleton : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (I : Type) [Finite I] (u : I → V), v.Integers O → Module.finrank C V = 1 → (∃ i, u i ≠ 0) → ∃ w : V, w ≠ 0 ∧ Submodule.span O (Set.range u) = Submodule.span O {w} := by
  atlas_forward_decl GlobalTheory.finGen_line_span_principal_target
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem detLattice_eq_span_singleton : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → Module.finrank C (detLine C ρ τ N) = 1 ∧ ∃ w : detLine C ρ τ N, w ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {w} := by
  intro C _ v O _ _ Λ _ h N hv ρ τ hind htop hN
  obtain ⟨π, hπ, -, hq⟩ := GlobalTheory.T.eigen_projection_quotient_lattice C O Λ h ρ τ hind htop
  have hsurj : Function.Surjective π := fun x => ⟨x, hπ x⟩
  obtain ⟨g, hgC, hgO⟩ := GlobalTheory.T.exists_spanning_image_lattice C O (eig C ρ τ) h π hsurj
  have hq' : quotLattice C ρ τ = (Submodule.span O (Set.range g) : Set (eig C ρ τ)) := by
    rw [hq, hgO]
  obtain ⟨hrank, s, hs⟩ := GlobalTheory.T.exteriorPower_top_finrank_one C (eig C ρ τ) h N g hgC hN
  have hspan : detLattice C ρ τ N =
      Submodule.span O (Set.range (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s))) := by
    unfold detLattice
    rw [hq']
    exact GlobalTheory.T.exteriorPower_span_of_lattice C O (eig C ρ τ) h N g
  refine ⟨hrank, ?_⟩
  obtain ⟨w, hw, hwspan⟩ := GlobalTheory.T.rank_one_lattice_span_singleton C v O (⋀[C]^N (eig C ρ τ)) (Fin N → Fin h)
    (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s)) hv hrank ⟨s, hs⟩
  exact ⟨w, hw, hspan.trans hwspan⟩

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_lattice_principal : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → Module.finrank C (detLine C ρ τ N) = 1 ∧ ∃ w : detLine C ρ τ N, w ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {w} := by
  atlas_forward_decl GlobalTheory.detLattice_eq_span_singleton
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.DetLattice

theorem iota_image_detLattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
      [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N →
      ∀ (D : GlobalTheory.Sandwich.Datum ε h Λ) (τ : Λ →+* O) ι, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.IsIota C D τ N ι →
        ∃ lam : C, lam ≠ 0 ∧
          ι '' (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLattice C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D) τ N : Set (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLine C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D) τ N)) =
            (fun w => lam • w) '' (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLattice C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actH D) τ N : Set (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLine C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actH D) τ N)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D τ ι hι
  obtain ⟨⟨hTi, hTs, hTd⟩, ⟨hHi, hHs, hHd⟩⟩ := GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  obtain ⟨-, x, hx0, hxL⟩ := GlobalTheory.T.determinant_lattice_principal C v O Λ h N hv (actT D) τ hTi hTs (hTd τ)
  obtain ⟨hW, y, hy0, hyL⟩ := GlobalTheory.T.determinant_lattice_principal C v O Λ h N hv (actH D) τ hHi hHs (hHd τ)
  have hbij := (GlobalTheory.T.tilt_lattice_bound_second p C v O hv ε hε Λ N h hh D τ).2 ι hι
  obtain ⟨lam, hlam, -, himg⟩ :=
    GlobalTheory.injective_into_line_span_eq_smul_span C O _ _ ι x y hbij.1 hW hx0 hy0
  exact ⟨lam, hlam, by rw [hxL, hyL]; exact himg⟩

end GlobalTheory.DetLattice
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_lattice_bound_third : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
      [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N →
      ∀ (D : GlobalTheory.Sandwich.Datum ε h Λ) (τ : Λ →+* O) ι, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.IsIota C D τ N ι →
        ∃ lam : C, lam ≠ 0 ∧
          ι '' (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLattice C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D) τ N : Set (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLine C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D) τ N)) =
            (fun w => lam • w) '' (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLattice C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actH D) τ N : Set (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLine C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actH D) τ N)) := by
  atlas_forward_decl GlobalTheory.DetLattice.iota_image_detLattice
end

section
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] {C : Type} [Field C] [Algebra O C]

theorem incl_apply' (h : ℕ) (l : Fin h → O) : incl C h l = fun i => algebraMap O C (l i) := rfl

theorem incl_mem_eig {Λ : Type} [CommRing Λ] {h : ℕ} (ρ : Λ → Matrix (Fin h) (Fin h) O)
    (σ : Λ →+* O) (l : Fin h → O) (hl : ∀ a, ρ a *ᵥ l = σ a • l) : incl C h l ∈ eig C ρ σ := by
  simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  intro a
  funext i
  have e := congrFun (hl a) i
  simp only [incl_apply', Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [← map_mul, ← e, RingHom.map_mulVec]
  rfl

end SlopeTestRemainingChoices

section Parts

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {C : Type} [Field C] [Algebra O C]
  {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

theorem card_eq_lieRank (hinj : Function.Injective (algebraMap O C)) (D : Datum ε h Λ)
    (τ : Λ →+* O) {a : ℕ} (x : Fin a → Fin h → C) (hx : IsBasisOf C (lieSub C D τ) x) :
    a = D.lieRank τ := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  have hincl : Function.Injective (incl C h : (Fin h → O) →ₗ[O] (Fin h → C)) := by
    intro u u' e
    funext i
    exact hinj (congrFun e i)
  have hliO : LinearIndependent O x := by
    refine hx.1.restrict_scalars ?_
    intro r s e
    apply hinj
    simpa [Algebra.algebraMap_eq_smul_one] using e
  have h1 : Module.finrank O (lieSub C D τ) = a := by
    rw [← hx.2, finrank_span_eq_card hliO, Fintype.card_fin]
  have h2 : Module.finrank O ↥(D.Lie ⊓ D.Tsub τ) = Module.finrank O (lieSub C D τ) :=
    (Submodule.equivMapOfInjective _ hincl _).finrank_eq
  unfold Datum.lieRank
  rw [h2, h1]

theorem span_eigPart_top (D : Datum ε h Λ) (τ : Λ →+* O)
    (hind : iSupIndep (fun σ : Λ →+* O => eig C (actT D) σ))
    (htop : (⨆ σ : Λ →+* O, eig C (actT D) σ) = ⊤) {n : ℕ} (u : Fin n → Fin h → C)
    (hu : Submodule.span O (Set.range u) = eigPart C (actT D) τ ⊤) (hue : ∀ i, u i ∈ eig C (actT D) τ) :
    Submodule.span C (Set.range u) = eig C (actT D) τ := by
  set S := Submodule.span C (Set.range u) with hSdef
  set R := ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C (actT D) σ.1 with hRdef
  have hSle : S ≤ eig C (actT D) τ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hue i
  have hdisj : Disjoint (eig C (actT D) τ) R :=
    (hind τ).mono_right (iSup_le fun σ => le_iSup₂_of_le (f := fun j (_ : j ≠ τ) => eig C (actT D) j) σ.1 σ.2 le_rfl)
  have htop' : eig C (actT D) τ ⊔ R = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← htop]
    refine iSup_le fun σ => ?_
    by_cases hσ : σ = τ
    · subst hσ
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun σ : {σ : Λ →+* O // σ ≠ τ} => eig C (actT D) σ.1) ⟨σ, hσ⟩)
  have hS : ∀ z, z ∈ eigPart C (actT D) τ ⊤ → z ∈ S := by
    intro z hz
    rw [← hu] at hz
    exact Submodule.span_le_restrictScalars O C _ hz
  have hall : (⊤ : Submodule C (Fin h → C)) ≤ S ⊔ R := by
    rw [← (Pi.basisFun C (Fin h)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hej : (Pi.basisFun C (Fin h) j) ∈ eig C (actT D) τ ⊔ R := by
      rw [htop']
      trivial
    obtain ⟨y, hy, r, hr, hyr⟩ := Submodule.mem_sup.1 hej
    have hy' : y ∈ eigPart C (actT D) τ ⊤ := by
      refine Submodule.mem_inf.2 ⟨hy, ?_⟩
      refine Submodule.mem_sup.2 ⟨Pi.basisFun C (Fin h) j, ⟨Pi.single j 1, trivial, ?_⟩, -r,
        Submodule.neg_mem _ hr, by rw [← hyr]; abel⟩
      funext k
      by_cases hk : k = j
      · subst hk
        simp [incl_apply']
      · simp [incl_apply', Pi.single_apply, hk]
    exact Submodule.mem_sup.2 ⟨y, hS y hy', r, hr, hyr⟩
  refine le_antisymm hSle fun z hz => ?_
  have hz' : z ∈ (S ⊔ R) ⊓ eig C (actT D) τ := ⟨hall trivial, hz⟩
  rwa [sup_inf_assoc_of_le R hSle, hdisj.symm.eq_bot, sup_bot_eq] at hz'

end Parts

theorem lieRank_add_card_and_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) (a b : ℕ) (x : Fin a → Fin h → C) (w : Fin a → Fin h → C) (n : Fin b → Fin h → C), IsBasisOf C (lieSub C D τ) x → IsBasisOf C (wQuot C D τ) w → IsBasisOf C (alQuot C D τ) n → a = D.lieRank τ ∧ a + b = N ∧ ∀ i, ∃ y : eig C (actH D) τ, bC C D y = x i := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D τ a b x w n hx hw hn
  obtain ⟨⟨hindT, htopT, hdimT⟩, ⟨hindH, htopH, hdimH⟩⟩ :=
    GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  refine ⟨card_eq_lieRank hv.hom_inj D τ x hx, ?_, ?_⟩
  · obtain ⟨u, -, -, hu, -⟩ := GlobalTheory.T.dvr_determinant_product_orders p C v O hv ε hε Λ a b h D τ w n hw hn
    have hspan := span_eigPart_top D τ hindT htopT (fun i => (u i : Fin h → C)) hu.2
      (fun i => (u i).2)
    have e := finrank_span_eq_card hu.1
    rw [hspan, hdimT τ, Fintype.card_fin] at e
    exact e.symm
  · intro i
    have hint := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
    have hX : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
        actT D l * D.G.map (WittVector.fontaineTheta O p) := by
      intro l
      have e' := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (hint.2.2.1 l)
      simp only [Matrix.map_mul] at e'
      unfold actH actT
      rw [e']
      simp only [rhoTA, Matrix.map_map]
      rfl
    have hmap := (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D)
      (D.G.map (WittVector.fontaineTheta O p)) hX).2 htopH hindT τ
    have hbC : bC C D = Matrix.toLin' ((D.G.map (WittVector.fontaineTheta O p)).map (algebraMap O C)) :=
      rfl
    have hxi : x i ∈ lieSub C D τ := hx.2 ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨l, ⟨hlL, hlT⟩, hl⟩ := Submodule.mem_map.1 hxi
    obtain ⟨m, rfl⟩ := hlL
    have hT : incl C h (D.bb m) ∈ eig C (actT D) τ := by
      refine incl_mem_eig _ _ _ fun c => ?_
      have := (Submodule.mem_iInf _).1 hlT c
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
      exact this
    have hR : incl C h (D.bb m) ∈ LinearMap.range (bC C D) := by
      refine ⟨incl C h m, ?_⟩
      funext k
      rw [hbC, Matrix.toLin'_apply, incl_apply', incl_apply']
      show _ = algebraMap O C ((D.G.map (WittVector.fontaineTheta O p) *ᵥ m) k)
      rw [RingHom.map_mulVec]
      rfl
    rw [hbC] at hR
    have hmem := hmap ▸ (Submodule.mem_inf.2 ⟨hR, hT⟩)
    obtain ⟨y, hy, hyeq⟩ := Submodule.mem_map.1 hmem
    exact ⟨⟨y, hy⟩, by rw [hbC]; exact hyeq.trans hl⟩

end GlobalTheory.DetInv
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_determinant_frame_rank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) (a b : ℕ) (x : Fin a → Fin h → C) (w : Fin a → Fin h → C) (n : Fin b → Fin h → C), IsBasisOf C (lieSub C D τ) x → IsBasisOf C (wQuot C D τ) w → IsBasisOf C (alQuot C D τ) n → a = D.lieRank τ ∧ a + b = N ∧ ∀ i, ∃ y : eig C (actH D) τ, bC C D y = x i := by
  atlas_forward_decl GlobalTheory.DetInv.lieRank_add_card_and_lift
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_alpha_determinant_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (a b h : ℕ), h = Module.finrank ℤ_[p] Λ * (a + b) → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) (z : Fin (a + b) → eig C (actH D) τ), IsBasisOf C (lieSub C D τ) (fun i => bC C D (z (Fin.castAdd b i))) → IsBasisOf C (filQuot C D τ) (fun i => (z (Fin.natAdd a i) : Fin h → C)) → ∃ c : C, v c = ∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ}, v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 ∧ (Submodule.span O {exteriorPower.ιMulti C (a + b) z} : Set (detLine C (actH D) τ (a + b))) = (fun w => c • w) '' (detLattice C (actH D) τ (a + b) : Set (detLine C (actH D) τ (a + b))) := by
  first | exact @GlobalTheory.DetInv.span_wedge_lie_fil_eq_smul_detLattice | exact GlobalTheory.DetInv.span_wedge_lie_fil_eq_smul_detLattice | (intros; apply GlobalTheory.DetInv.span_wedge_lie_fil_eq_smul_detLattice <;> assumption)
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.ShiftLam

theorem ιMulti_sum_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (z : Fin n → V) :
    exteriorPower.ιMulti K n (fun i => ∑ j, M i j • z j) = M.det • exteriorPower.ιMulti K n z := by
  have hA : (exteriorPower.ιMulti K n).compLinearMap (Fintype.linearCombination K z) =
      (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K).smulRight
        (exteriorPower.ιMulti K n z) := by
    refine (Pi.basisFun K (Fin n)).ext_alternating fun u hu => ?_
    let s : Equiv.Perm (Fin n) := Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)
    have e : (fun i => Pi.basisFun K (Fin n) (u i)) = (fun i => Pi.basisFun K (Fin n) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K)
        (fun i => Pi.basisFun K (Fin n) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp
  exact AlternatingMap.congr_fun hA M

theorem val_le_of_image_subset {C O W : Type} [Field C] [CommRing O] [Algebra O C]
    [AddCommGroup W] [Module C W] [Module O W] [IsScalarTower O C W]
    (v : Valuation C NNReal) (hv : v.Integers O) {e : W} (he : e ≠ 0) {μ l : C}
    (H : (fun w => l • w) '' (Submodule.span O {e} : Set W) ⊆
      (fun w => μ • w) '' (Submodule.span O {e} : Set W)) :
    v l ≤ v μ := by
  obtain ⟨w, hw, hwe⟩ := H ⟨e, Submodule.subset_span rfl, rfl⟩
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hmu : μ * algebraMap O C o = l := by
    apply smul_left_injective C he
    simp only [mul_smul, algebraMap_smul]
    exact hwe
  rw [← hmu, map_mul]
  exact mul_le_of_le_one_right (by positivity) (hv.map_le_one o)

end GlobalTheory.ShiftLam

namespace GlobalTheory.ShiftLam

theorem ringHom_eq_of_apply_gen {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (α : Λ)
    (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (σ τ : Λ →+* O) (he : σ α = τ α) : σ = τ := by
  let S : Subalgebra ℤ_[p] Λ :=
    { σ.eqLocus τ with
      algebraMap_mem' := fun r => by
        show σ (algebraMap ℤ_[p] Λ r) = τ (algebraMap ℤ_[p] Λ r)
        have h1 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (σ.comp (algebraMap ℤ_[p] Λ))
        have h2 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (τ.comp (algebraMap ℤ_[p] Λ))
        exact (RingHom.congr_fun h1 r).trans (RingHom.congr_fun h2 r).symm }
  have hle : Algebra.adjoin ℤ_[p] {α} ≤ S := Algebra.adjoin_le (by simpa [S] using he)
  ext x
  have hx : x ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
  exact hle hx

end GlobalTheory.ShiftLam

theorem GlobalTheory.DetInv.isShift_of_iota_image : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → IsShift C v D τ (v lam * (∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ}, v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1)⁻¹) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ α hα N h hh D τ ι lam hι hlat
  unfold IsShift
  intro a b x g m k hx hgx hm hkm
  obtain ⟨ha, hab, hy⟩ := GlobalTheory.T.dvr_determinant_frame_rank p C v O hv ε hε Λ N h hh D τ a b x _ _ hx hgx hkm
  subst hab
  choose y hy using hy
  obtain ⟨X, hX1, hX2, -, hXdet⟩ := GlobalTheory.T.dvr_determinant_product_orders p C v O hv ε hε Λ a b h D τ _ _ hgx hkm
  have hmem : ∀ j, m j ∈ eig C (actH D) τ := fun j => by
    have : m j ∈ filQuot C D τ := hm.2 ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this.1
  let z : Fin (a + b) → eig C (actH D) τ := Fin.append y (fun j => ⟨m j, hmem j⟩)
  have hz1 : ∀ i, z (Fin.castAdd b i) = y i := fun i => Fin.append_left _ _ _
  have hz2 : ∀ j, (z (Fin.natAdd a j) : Fin h → C) = m j := fun j => by
    simp [z, Fin.append_right]
  obtain ⟨c, hc, hcz⟩ := GlobalTheory.T.dvr_alpha_determinant_order p C v O hv ε hε Λ α hα a b h hh D τ z
    (by convert hx using 1; funext i; rw [hz1, hy]) (by convert hm using 1; funext j; exact hz2 j)
  let M : Matrix (Fin (a + b)) (Fin (a + b)) C :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 k)
  have hM : M.det = g.det * k.det := by
    simp only [M, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  let Y : Fin (a + b) → eig C (actH D) τ := fun i => ∑ j, M i j • z j
  have hY1 : ∀ i, Y (Fin.castAdd b i) = ∑ j, g i j • y j := fun i => by
    simp [Y, M, Fin.sum_univ_add, hz1]
  have hY2 : ∀ i, Y (Fin.natAdd a i) = ∑ j, k i j • z (Fin.natAdd a j) := fun i => by
    simp [Y, M, Fin.sum_univ_add]
  have hιX : ι (exteriorPower.ιMulti C (a + b) X) = exteriorPower.ιMulti C (a + b) Y := by
    apply hι
    · intro i hi
      rw [← ha] at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin a, Fin.castAdd b i' = i := ⟨⟨i, hi⟩, rfl⟩
      rw [hX1, hY1]
      simp [hy]
    · intro i hi
      rw [← ha] at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin b, Fin.natAdd a i' = i :=
        ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
      rw [hX2, hY2]
      simp [hz2]
  have hYz : exteriorPower.ιMulti C (a + b) Y =
      (g.det * k.det) • exteriorPower.ιMulti C (a + b) z := by
    rw [← hM]; exact GlobalTheory.ShiftLam.ιMulti_sum_smul M z
  have himg : ι '' (detLattice C (actT D) τ (a + b) : Set (detLine C (actT D) τ (a + b))) =
      (fun w => (g.det * k.det) • w) ''
        (Submodule.span O {exteriorPower.ιMulti C (a + b) z} : Set (detLine C (actH D) τ (a + b))) := by
    rw [hXdet]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hu
      refine ⟨o • exteriorPower.ιMulti C (a + b) z,
        Submodule.smul_mem _ _ (Submodule.subset_span rfl), ?_⟩
      show _ = ι _
      rw [LinearMap.map_smul_of_tower, hιX, hYz, smul_comm]
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hu
      refine ⟨o • exteriorPower.ιMulti C (a + b) X,
        Submodule.smul_mem _ _ (Submodule.subset_span rfl), ?_⟩
      show ι _ = _
      rw [LinearMap.map_smul_of_tower, hιX, hYz, smul_comm]
  obtain ⟨hind, hsup, hrk⟩ := (GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ (a + b) h hh D).2
  obtain ⟨e, -, -, he, hdet⟩ := GlobalTheory.T.exists_basis_quotient_lattice_eigen C v O Λ h (a + b) hv (actH D) τ hind hsup (hrk τ)
  have hfin : (fun w => (g.det * k.det * c) • w) ''
      (Submodule.span O {exteriorPower.ιMulti C (a + b) e} : Set (detLine C (actH D) τ (a + b))) =
      (fun w => lam • w) ''
      (Submodule.span O {exteriorPower.ιMulti C (a + b) e} : Set (detLine C (actH D) τ (a + b))) := by
    rw [← hdet, ← hlat, himg, hcz, Set.image_image]
    simp only [smul_smul]
  have hval : v (g.det * k.det * c) = v lam :=
    le_antisymm (GlobalTheory.ShiftLam.val_le_of_image_subset v hv he hfin.subset)
      (GlobalTheory.ShiftLam.val_le_of_image_subset v hv he hfin.symm.subset)
  have hc0 : v c ≠ 0 := by
    rw [hc]
    refine finprod_induction (fun t : NNReal => t ≠ 0) one_ne_zero (fun s t => mul_ne_zero) ?_
    intro σ
    refine pow_ne_zero _ ((Valuation.ne_zero_iff v).2 (sub_ne_zero.2 fun hst => σ.2 ?_))
    exact GlobalTheory.ShiftLam.ringHom_eq_of_apply_gen α hα σ.1 τ (hv.hom_inj hst).symm
  rw [← hc, ← hval, map_mul, map_mul, mul_inv_cancel_right₀ hc0]
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_alpha_determinant_valuation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → IsShift C v D τ (v lam * (∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ}, v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1)⁻¹) := by
  atlas_forward_decl GlobalTheory.DetInv.isShift_of_iota_image
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.MonoGen

theorem exists_adjoin_eq_top_padicInt : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ],
    ∃ α : Λ, Algebra.adjoin ℤ_[p] {α} = ⊤ := by
  intro p _ Λ _ _ _ _ _ _
  have hinj : Function.Injective (algebraMap ℤ_[p] Λ) := FaithfulSMul.algebraMap_injective _ _
  haveI : Algebra.IsIntegral ℤ_[p] Λ := Algebra.IsIntegral.of_finite ℤ_[p] Λ
  haveI : IsLocalHom (algebraMap ℤ_[p] Λ) :=
    RingHom.IsIntegral.isLocalHom (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) (A := Λ)) hinj
  haveI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  exact Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top hinj

end GlobalTheory.MonoGen
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem ringHom_eq_of_eq_on_generator {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    {α : Λ} (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (σ τ : Λ →+* O) (h : σ α = τ α) : σ = τ := by
  have hbase : σ.comp (algebraMap ℤ_[p] Λ) = τ.comp (algebraMap ℤ_[p] Λ) :=
    GlobalTheory.padicInt_ringHom_ext_of_isHausdorff p O _ _
  ext x
  have hx : x ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (fun y hy => ?_) (fun r => ?_) (fun y z _ _ hy hz => ?_)
    (fun y z _ _ hy hz => ?_) hx
  · rw [Set.mem_singleton_iff.1 hy]; exact h
  · exact congrArg (fun f : ℤ_[p] →+* O => f r) hbase
  · rw [map_add, map_add, hy, hz]
  · rw [map_mul, map_mul, hy, hz]

theorem shift_linear_isom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), ∃ r : NNReal, r ≠ 0 ∧ IsShift C v D ((γ : O →+* O).comp τ₀) r ∧ Real.log r = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  classical
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ τ₀
  obtain ⟨α, hα⟩ := GlobalTheory.MonoGen.exists_adjoin_eq_top_padicInt p Λ
  obtain ⟨κ₀, κ', hlin⟩ := GlobalTheory.T.psi_embedding_determinant_property p C v O hv ε hε Λ τ₀
  obtain ⟨hfin, -⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  haveI := hfin
  letI := Fintype.ofFinite (Λ →+* O)
  let c : (Λ →+* O) → ℝ := fun σ => if σ = τ₀ then 0 else
    Real.log (v (algebraMap O C (τ₀ α) - algebraMap O C (σ α)))
  refine ⟨κ₀, fun σ => κ' σ - c σ, ?_⟩
  intro γ hγ N h hh D
  obtain ⟨γC, hγC, hvγ⟩ := hγ
  set τ : Λ →+* O := (γ : O →+* O).comp τ₀ with hτ
  obtain ⟨⟨ι, hι, -⟩, -⟩ := GlobalTheory.T.tilt_lattice_bound_second p C v O hv ε hε Λ N h hh D τ
  obtain ⟨lam, hlam, hlat⟩ := GlobalTheory.T.tilt_lattice_bound_third p C v O hv ε hε Λ N h hh D τ ι hι
  have hsh := GlobalTheory.T.dvr_alpha_determinant_valuation p C v O hv ε hε Λ α hα N h hh D τ ι lam hι hlat
  have hlog := hlin γ ⟨γC, hγC, hvγ⟩ N h hh D ι lam hι hlam hlat

  have hsep : ∀ σ : Λ →+* O, σ ≠ τ →
      v (algebraMap O C (τ α) - algebraMap O C (σ α)) ≠ 0 := by
    intro σ hσ
    refine (Valuation.ne_zero_iff v).mpr ?_
    rw [← map_sub]
    intro h0
    apply hσ
    refine (ringHom_eq_of_eq_on_generator hα σ τ ?_)
    have h1 : τ α - σ α = 0 := hv.hom_inj (by rw [h0, map_zero])
    exact (sub_eq_zero.1 h1).symm
  have hv0 : v lam ≠ 0 := (Valuation.ne_zero_iff v).mpr hlam
  set P : NNReal := ∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ},
    v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 with hP
  have hPe : P = ∏ σ : {σ : Λ →+* O // σ ≠ τ},
      v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 :=
    finprod_eq_prod_of_fintype _
  have hP0 : P ≠ 0 := by
    rw [hPe]
    exact Finset.prod_ne_zero_iff.mpr fun σ _ => pow_ne_zero _ (hsep σ.1 σ.2)
  refine ⟨v lam * P⁻¹, mul_ne_zero hv0 (inv_ne_zero hP0), hsh, ?_⟩

  have hlogP : Real.log (P : ℝ) = ∑ σ : {σ : Λ →+* O // σ ≠ τ},
      (D.lieRank σ.1 : ℝ) * Real.log (v (algebraMap O C (τ α) - algebraMap O C (σ.1 α))) := by
    rw [hPe, NNReal.coe_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      rw [NNReal.coe_pow, Real.log_pow]
    · intro σ _
      exact_mod_cast pow_ne_zero _ (hsep σ.1 σ.2)
  have hlr : Real.log ((v lam * P⁻¹ : NNReal) : ℝ) = Real.log (v lam) - Real.log (P : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_inv, Real.log_mul, Real.log_inv, sub_eq_add_neg]
    · exact_mod_cast hv0
    · exact inv_ne_zero (by exact_mod_cast hP0)

  let e : (Λ →+* O) ≃ (Λ →+* O) :=
    { toFun := fun σ => (γ : O →+* O).comp σ
      invFun := fun σ => (γ.symm : O →+* O).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  have hsub : ∑ σ : {σ : Λ →+* O // σ ≠ τ},
      (D.lieRank σ.1 : ℝ) * Real.log (v (algebraMap O C (τ α) - algebraMap O C (σ.1 α))) =
      ∑ σ : Λ →+* O, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * c σ := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun σ => σ ≠ τ) (by simp)
      (fun σ => (D.lieRank σ : ℝ) * Real.log (v (algebraMap O C (τ α) - algebraMap O C (σ α)))),
      Finset.sum_filter]
    symm
    refine Fintype.sum_equiv e _ _ fun σ => ?_
    show (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * c σ = if (γ : O →+* O).comp σ ≠ τ then _ else 0
    by_cases hσ : σ = τ₀
    · have heq : (γ : O →+* O).comp σ = τ := by rw [hσ]
      rw [if_neg (not_not.2 heq)]
      simp only [c, if_pos hσ, mul_zero]
    · have hne : (γ : O →+* O).comp σ ≠ τ := by
        intro heq
        apply hσ
        ext x
        exact γ.injective (congrArg (fun f : Λ →+* O => f x) heq)
      rw [if_pos hne]
      simp only [c, if_neg hσ]
      have hiso : v (algebraMap O C (τ₀ α) - algebraMap O C (σ α)) =
          v (algebraMap O C (γ (τ₀ α)) - algebraMap O C (γ (σ α))) := by
        rw [← hγC, ← hγC, ← map_sub γC, hvγ]
      rw [hiso]
      rfl
  rw [hlr, hlogP, hsub, hlog, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_embedding_determinant_value : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), ∃ r : NNReal, r ≠ 0 ∧ IsShift C v D ((γ : O →+* O).comp τ₀) r ∧ Real.log r = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  atlas_forward_decl GlobalTheory.DetInv.shift_linear_isom
end
