import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestriction
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAddEquiv
import Development.WeilBound.CoreStatements.HodgeTatePoints.RfTors
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.HodgeTatePoints.LiftComul
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrder
import Development.WeilBound.CoreStatements.HodgeTatePoints.TensorSpanLe
import Development.WeilBound.CoreStatements.HodgeTatePoints.RhPull

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ K : AddSubgroup N, IsFinFlatSub G (T.A ⧸ vanIdeal T pt K) (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) := by
  classical
  intro p _ C _ _ _ v R _ _ hv hp G _ _ T N _ _ _ pt hpt K
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : ValuationRing R := ValuationRing.iff_dvd_total.mpr ⟨fun a b => by
    rcases le_total (v (algebraMap R C a)) (v (algebraMap R C b)) with h | h
    · exact Or.inr (hv.dvd_of_le h)
    · exact Or.inl (hv.dvd_of_le h)⟩
  haveI : IsLocalRing R := ValuationRing.isLocalRing R
  haveI : IsBezout R := ValuationRing.instIsBezout
  haveI : Module.Finite R T.A := T.fin
  set I : Ideal T.A := vanIdeal T pt (K : Set N) with hI
  have hpts : ∀ x : N, pt x ^ p = 1 := fun x => (hpt.range (pt x)).mpr ⟨x, rfl⟩
  choose ev hev using fun x : N => (T.univ R (pt x) (hpts x)).exists
  have huniq : ∀ (x : N) (φ : T.A →ₐ[R] R), spMap φ ≫ T.y = pt x → φ = ev x :=
    fun x φ h => (T.univ R (pt x) (hpts x)).unique h (hev x)
  have memI : ∀ a : T.A, a ∈ I ↔ ∀ k ∈ K, ev k a = 0 := by
    intro a
    constructor
    · intro ha k hk
      have ha' : ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0 := ha
      exact ha' k hk (ev k) (hev k)
    · intro ha
      show ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0
      intro k hk φ hφ
      rw [huniq k φ hφ]
      exact ha k hk
  obtain ⟨evbar, hevbar⟩ : ∃ e : K → ((T.A ⧸ I) →ₐ[R] R),
      ∀ k, (e k).comp (Ideal.Quotient.mkₐ R I) = ev k :=
    ⟨fun k => Ideal.Quotient.liftₐ I (ev k) (fun a ha => (memI a).mp ha k k.2),
      fun k => Ideal.Quotient.liftₐ_comp _ _ _⟩
  have hsep1 : ∀ b : T.A ⧸ I, (∀ k : K, evbar k b = 0) → b = 0 := by
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I b
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, memI]
    intro k hk
    have h1 := hb ⟨k, hk⟩
    rw [← AlgHom.comp_apply, hevbar] at h1
    exact h1
  have htors : Submodule.torsion R (T.A ⧸ I) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff b).mp hb
    rw [Submodule.mem_bot]
    refine hsep1 b fun k => ?_
    have h1 := congrArg (evbar k) hr
    rw [map_zero, Submonoid.smul_def, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero r)
  haveI : Module.Flat R (T.A ⧸ I) := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr htors
  haveI : Module.Finite R (T.A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ_surjective R I)
  haveI : Module.Free R (T.A ⧸ I) := Module.free_of_flat_of_isLocalRing
  have h0 : pt 0 = 1 := mul_left_cancel (a := pt 0) (by rw [_root_.mul_one, ← hpt.add, add_zero])
  have hneg : ∀ x, pt (-x) = (pt x)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hpt.add, neg_add_cancel, h0])
  have hE : ∀ k : K, spMap (evbar k) ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y = pt k := by
    intro k
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hevbar, hev]
  have hpowA : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀ := R) T.A), (f ≫ T.y) ^ p = 1 :=
    fun f => by rw [← CategoryTheory.MonObj.comp_pow, T.y_p, CategoryTheory.MonObj.comp_one]
  have hu : (spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1 := hpowA _
  have hpowc : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀ := R) (T.A ⧸ I)),
      (f ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1 :=
    fun f => by rw [← CategoryTheory.MonObj.comp_pow, hu, CategoryTheory.MonObj.comp_one]
  obtain ⟨Λ, hΛt⟩ : ∃ L : K → K → (TensorProduct R (T.A ⧸ I) (T.A ⧸ I) →ₐ[R] R),
      ∀ k1 k2 x y, L k1 k2 (TensorProduct.tmul R x y) = evbar k1 x * evbar k2 y :=
    ⟨fun k1 k2 => Algebra.TensorProduct.lift (evbar k1) (evbar k2) (fun _ _ => Commute.all _ _),
      fun _ _ _ _ => Algebra.TensorProduct.lift_tmul _ _ _ _ _⟩
  have hΛL : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeLeft = evbar k1 := fun k1 k2 =>
    AlgHom.ext fun b => by simp [hΛt]
  have hΛR : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeRight = evbar k2 := fun k1 k2 =>
    AlgHom.ext fun b => by simp [hΛt]
  have hι : Function.Injective (Pi.algHom R (fun _ : K => R) evbar).toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    exact hsep1 b fun k => by simpa using congrFun hb k
  have key : ∀ (w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) (k1 k2 : K),
      (Pi.algHom R (fun _ : K => R) evbar).toLinearMap
        (TensorProduct.piScalarRight R R (T.A ⧸ I) K
          (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) k2) k1 =
        Λ k1 k2 w := by
    intro w k1 k2
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hΛt, TensorProduct.piScalarRight_apply, mul_comm]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hsep2 : ∀ w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I), (∀ k1 k2 : K, Λ k1 k2 w = 0) → w = 0 := by
    intro w hw
    have h1 : TensorProduct.piScalarRight R R (T.A ⧸ I) K
        (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) = 0 := by
      funext k2
      apply hι
      funext k1
      rw [key, hw]
      simp
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap _ hι) w h1
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro S _ _ φ φ' hφ
    have e1 : spMap (φ.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y =
        spMap (φ'.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y := by
      rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
        Category.assoc, hφ]
    have e2 := (T.univ S _ (hpowA (spMap (φ.comp (Ideal.Quotient.mkₐ R I))))).unique rfl e1.symm
    refine AlgHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I b
    exact DFunLike.congr_fun e2 a
  · intro S _ _
    refine ⟨(Algebra.ofId R S).comp (evbar 0), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hE]
    show spMap (Algebra.ofId R S) ≫ pt 0 = 1
    rw [h0, CategoryTheory.MonObj.comp_one]
  · have hm : ((spMap (Algebra.TensorProduct.includeLeft : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫
          spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) *
        (spMap (Algebra.TensorProduct.includeRight : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫
          spMap (Ideal.Quotient.mkₐ R I) ≫ T.y)) ^ p = 1 := by
      rw [mul_pow, hpowc, hpowc, _root_.one_mul]
    obtain ⟨ψ0, hψ0⟩ := (T.univ _ _ hm).exists
    have hψI : ∀ a ∈ I, ψ0 a = 0 := by
      intro a ha
      refine hsep2 _ fun k1 k2 => ?_
      have e : spMap ((Λ k1 k2).comp ψ0) ≫ T.y = pt ((k1 : N) + k2) := by
        rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.MonObj.comp_mul,
          ← Category.assoc (spMap (Λ k1 k2)) (spMap Algebra.TensorProduct.includeLeft),
          ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hΛL, hE,
          ← Category.assoc (spMap (Λ k1 k2)) (spMap Algebra.TensorProduct.includeRight),
          ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hΛR, hE, hpt.add]
      rw [← AlgHom.comp_apply, huniq _ _ e]
      exact (memI a).mp ha _ (K.add_mem k1.2 k2.2)
    intro S _ _ φ φ'
    have hLR : (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp
        Algebra.TensorProduct.includeRight = φ' := AlgHom.ext fun b => by simp
    refine ⟨(Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp
      (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
      ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
      Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.MonObj.comp_mul]
    rw [← Category.assoc (spMap (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)))
        (spMap Algebra.TensorProduct.includeLeft),
      ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Algebra.TensorProduct.lift_comp_includeLeft,
      ← Category.assoc (spMap (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)))
        (spMap Algebra.TensorProduct.includeRight),
      ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hLR]
  · have hinv : ((spMap (Ideal.Quotient.mkₐ R I) ≫ T.y)⁻¹) ^ p = 1 := by rw [inv_pow, hu, inv_one]
    obtain ⟨ψ0, hψ0⟩ := (T.univ (T.A ⧸ I) _ hinv).exists
    have hψI : ∀ a ∈ I, ψ0 a = 0 := by
      intro a ha
      refine hsep1 _ fun k => ?_
      have e : spMap ((evbar k).comp ψ0) ≫ T.y = pt (-(k : N)) := by
        rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.GrpObj.comp_inv,
          hE, hneg]
      rw [← AlgHom.comp_apply, huniq _ _ e]
      exact (memI a).mp ha _ (K.neg_mem k.2)
    intro S _ _ φ
    refine ⟨φ.comp (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
      ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
      Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.GrpObj.comp_inv, inv_mul_cancel]
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_finite_flat_subgroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ K : AddSubgroup N, IsFinFlatSub G (T.A ⧸ vanIdeal T pt K) (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  intro p _ C _ _ _ v R _ _ _ _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj
  haveI := hj
  have hex : ∀ x : N, ∃ y : N', pt' y = pt x ≫ j := by
    intro x
    apply (hpt'.range _).1
    have hx : (pt x) ^ p = 1 := (hpt.range _).2 ⟨x, rfl⟩
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  choose f hf using hex
  have hadd : ∀ x y : N, f (x + y) = f x + f y := by
    intro x y
    apply hpt'.inj
    rw [hpt'.add, hf, hf, hf, hpt.add, MonObj.mul_comp]
  let jN : N →+ N' :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        simpa using h.symm
      map_add' := hadd }
  have hyp : (T.y ≫ j) ^ p = 1 := by
    rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp]
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) hyp
  refine ⟨jN, ψ, fun x => hf x, hψ, ?_⟩
  intro g hg
  obtain ⟨a, ha⟩ := hg
  refine ⟨ψ a, ?_⟩
  intro x φ hφ
  have key : spMap (φ.comp ψ) ≫ T'.y = pt' (jN x) := by
    rw [← Chart.spMap_comp ψ φ]
    change (spMap φ ≫ spMap ψ) ≫ T'.y = pt' (f x)
    rw [Category.assoc, hψ, ← Category.assoc, hφ, hf]
  exact ha (jN x) (φ.comp ψ) key
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∀ K : AddSubgroup N, (∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ G), z ≫ j = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S, spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z) → ∀ jN : N →+ N', (∀ x, pt' (jN x) = pt x ≫ j) → jN.ker = K ∧ ∀ g ∈ torsFun C T pt, (∀ k ∈ jN.ker, g k = 0) → g ∈ (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt := by
  intro p _ C _ _ _ v R _ _ hv _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj K hK jN hjN
  haveI := hj
  classical
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hpow : ∀ x, (pt x) ^ p = 1 := fun x => (hpt.range _).2 ⟨x, rfl⟩
  have hpow' : ∀ x, (pt' x) ^ p = 1 := fun x => (hpt'.range _).2 ⟨x, rfl⟩
  choose φ hφ hφu using fun x => T.univ R (pt x) (hpow x)
  choose φ' hφ' hφu' using fun x => T'.univ R (pt' x) (hpow' x)
  have h0' : pt' 0 = 1 := by
    have h := hpt'.add 0 0
    rw [add_zero] at h
    simpa using h.symm
  have hyp : (T.y ≫ j) ^ p = 1 := by
    rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp]
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) hyp
  have hcomp : ∀ x, (φ x).comp ψ = φ' (jN x) := by
    intro x
    apply hφu'
    rw [← Chart.spMap_comp ψ (φ x), Category.assoc, hψ, ← Category.assoc, hφ x, hjN]
  have hker : ∀ x, jN x = 0 ↔ pt x ≫ j = 1 := by
    intro x
    rw [← hjN, ← h0']
    exact hpt'.inj.eq_iff.symm
  have hfac : ∀ x, pt x ≫ j = 1 ↔ ∀ a ∈ vanIdeal T pt (K : Set N), φ x a = 0 := by
    intro x
    rw [hK R (pt x)]
    constructor
    · rintro ⟨χ, hχ⟩ a ha
      have e : χ.comp (Ideal.Quotient.mkₐ R (vanIdeal T pt (K : Set N))) = φ x := by
        apply hφu
        rw [← Chart.spMap_comp, Category.assoc]
        exact hχ
      rw [← e, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    · intro h
      refine ⟨Ideal.Quotient.liftₐ _ (φ x) h, ?_⟩
      rw [← Category.assoc, Chart.spMap_comp, Ideal.Quotient.liftₐ_comp]
      exact hφ x
  have hK1 : jN.ker = K := by
    ext x
    rw [AddMonoidHom.mem_ker, hker, hfac]
    constructor
    · intro h
      by_contra hx
      have hne : ∀ k ∈ K, ∃ c : T.A, φ k c ≠ φ x c := by
        intro k hk
        by_contra hall
        push_neg at hall
        have e1 : φ k = φ x := AlgHom.ext hall
        have e2 : pt k = pt x := by rw [← hφ k, ← hφ x, e1]
        exact hx (hpt.inj e2 ▸ hk)
      choose! c hc using hne
      let a : T.A := ∏ k ∈ Finset.univ.filter (· ∈ K), (c k - algebraMap R T.A (φ k (c k)))
      have ha : a ∈ vanIdeal T pt (K : Set N) := by
        rw [PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ]
        intro k hk
        simp only [a, map_prod]
        apply Finset.prod_eq_zero (i := k)
        · simpa using hk
        · simp
      have h1 := h a ha
      apply_fun algebraMap R C at h1
      simp only [a, map_prod, map_sub, AlgHom.commutes, map_zero] at h1
      rw [Finset.prod_eq_zero_iff] at h1
      obtain ⟨k, hk, hk0⟩ := h1
      rw [sub_eq_zero] at hk0
      exact hc k (by simpa using hk) (hinj (by simpa using hk0)).symm
    · intro hx a ha
      exact (PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ _ a).1 ha x hx
  refine ⟨hK1, ?_⟩
  intro g hg hgK
  rw [PositivityTheory.HtPt.Rf.mem_torsFun T hφ] at hg
  obtain ⟨a, rfl⟩ := hg
  have haI : a ∈ vanIdeal T pt (K : Set N) := by
    rw [PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ]
    intro k hk
    have h3 := hgK k (by rw [hK1]; exact hk)
    exact hinj (by rw [map_zero]; exact h3)
  obtain ⟨J, hJ⟩ : ∃ J : Ideal T.A, J = Ideal.map ψ (RingHom.ker (φ' 0)) := ⟨_, rfl⟩
  have hIJ : vanIdeal T pt (K : Set N) ≤ J := by
    have hzp : (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ^ p = 1 := by
      rw [← MonObj.comp_pow, T.y_p, MonObj.comp_one]
    have hqψ : (Ideal.Quotient.mkₐ R J).comp ψ = (Algebra.ofId R (T.A ⧸ J)).comp (φ' 0) := by
      apply AlgHom.ext
      intro b
      have hb : b - algebraMap R T'.A (φ' 0 b) ∈ RingHom.ker (φ' 0) := by
        simp [RingHom.mem_ker]
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply,
        ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, ← AlgHom.commutes ψ, ← map_sub, hJ]
      exact Ideal.mem_map_of_mem _ hb
    have hz1 : (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ≫ j = 1 := by
      calc (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ≫ j
          = spMap (Ideal.Quotient.mkₐ R J) ≫ spMap ψ ≫ T'.y := by rw [Category.assoc, hψ]
        _ = spMap ((Ideal.Quotient.mkₐ R J).comp ψ) ≫ T'.y := by
          rw [← Category.assoc, Chart.spMap_comp]
        _ = spMap ((Algebra.ofId R (T.A ⧸ J)).comp (φ' 0)) ≫ T'.y := by rw [hqψ]
        _ = spMap (Algebra.ofId R (T.A ⧸ J)) ≫ pt' 0 := by
          rw [← Chart.spMap_comp, Category.assoc, hφ' 0]
        _ = 1 := by rw [h0', MonObj.comp_one]
    obtain ⟨χ, hχ⟩ := (hK (T.A ⧸ J) (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y)).1 hz1
    obtain ⟨w, -, hu⟩ := T.univ (T.A ⧸ J) (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) hzp
    have e : χ.comp (Ideal.Quotient.mkₐ R (vanIdeal T pt (K : Set N))) = Ideal.Quotient.mkₐ R J := by
      rw [hu _ rfl]
      apply hu
      rw [← Chart.spMap_comp, Category.assoc]
      exact hχ
    intro b hb
    have h2 := AlgHom.congr_fun e b
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2.symm
  have ha : a ∈ J := hIJ haI
  rw [hJ] at ha
  change a ∈ Submodule.span T.A (⇑ψ '' (RingHom.ker (φ' 0) : Set T'.A)) at ha
  clear hgK haI hIJ hJ
  suffices H : ∀ c : T.A, (fun x => algebraMap R C (φ x (c * a))) ∈
      (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt by
    have H1 := H 1
    rwa [_root_.one_mul] at H1
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro c
    have e : (fun y => algebraMap R C (φ y (c * ψ b))) =
        (fun y => algebraMap R C (φ y (ψ b))) * (fun y => algebraMap R C (φ y c)) := by
      funext y
      simp [map_mul, mul_comm]
    rw [e]
    apply Submodule.mul_mem_mul
    · rw [Submodule.mem_map]
      refine ⟨fun y => algebraMap R C (φ' y b), ?_, ?_⟩
      · rw [augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
        refine ⟨(PositivityTheory.HtPt.Rf.mem_torsFun T' hφ' _).2 ⟨b, rfl⟩, ?_⟩
        rw [SetLike.mem_coe, RingHom.mem_ker] at hb
        simp only [hb, map_zero]
      · funext y
        rw [LinearMap.funLeft_apply, ← hcomp y, AlgHom.comp_apply]
    · exact (PositivityTheory.HtPt.Rf.mem_torsFun T hφ _).2 ⟨c, rfl⟩
  | zero =>
    intro c
    simp only [mul_zero, map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    intro c
    have h4 := Submodule.add_mem _ (hx c) (hy c)
    convert h4 using 1
    funext z
    simp [mul_add]
  | smul r x _ hx =>
    intro c
    convert hx (c * r) using 1
    funext z
    rw [smul_eq_mul, _root_.mul_assoc]
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_homomorphism_compatible : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∀ K : AddSubgroup N, (∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ G), z ≫ j = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S, spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z) → ∀ jN : N →+ N', (∀ x, pt' (jN x) = pt x ≫ j) → jN.ker = K ∧ ∀ g ∈ torsFun C T pt, (∀ k ∈ jN.ker, g k = 0) → g ∈ (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (A' : HopfOrder (C := C) R N') (j : N →+ N'), (∀ g ∈ A'.carrier, (fun x => g (j x)) ∈ AA.carrier) → (∀ g ∈ AA.carrier, (∀ k ∈ j.ker, g k = 0) → g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier) → A'.carrier.map (LinearMap.funLeft R C (j : N → N')) = invFun AA.carrier j.ker := by
  first | exact @PositivityTheory.HtPt.Rh.sub_closed | exact PositivityTheory.HtPt.Rh.sub_closed
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_pullback_along_hom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (A' : HopfOrder (C := C) R N') (j : N →+ N'), (∀ g ∈ A'.carrier, (fun x => g (j x)) ∈ AA.carrier) → (∀ g ∈ AA.carrier, (∀ k ∈ j.ker, g k = 0) → g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier) → A'.carrier.map (LinearMap.funLeft R C (j : N → N')) = invFun AA.carrier j.ker := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem genAF_of_map_eq_invFun : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K :=
  PositivityTheory.HtPt.Rh.sub_pull

end GlobalTheory.CompanionTheory.Ar.GR
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generation_along_invariants : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun
end

section
section
noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem one_comp_monHom {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    [IsMonHom f] : (1 : T ⟶ G) ≫ f = 1 := by
  simp [Hom.one_def]

theorem sub_abelianScheme : QuotientByFiniteFlatStatement → ZarhinStatement →
    HodgeTateDatumStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R →
    ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A →
    L.IsLB → Out.RelAmple A L → ∀ (T : TorsRep A p) (N : Type) [AddCommGroup N] [Fintype N]
    [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt →
    ∀ K : AddSubgroup N, GenAF p (torsFun C T pt) K := by
  intro hQ hZ hD p _ C _ _ _ v R _ _ hint hp hc A _ L hA hL hamp T N _ _ _ pt hpt K
  haveI : IsCommMonObj A := hA.comm
  have hsub := GlobalTheory.T.torsion_points_finite_flat_subgroup p C v R hint hp A T N pt hpt K
  obtain ⟨A', _, L', q, hA', hL', hamp', hq, -, -, -, hker⟩ := hQ R A L hA hL hamp _ _ hsub
  obtain ⟨P, i, r, hi, hr, hir⟩ := hZ C v R hint A' L' hA' hL' hamp'
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI := hq
  haveI := hi
  haveI := hr
  have hj : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
      z ≫ (q ≫ i) = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S,
        spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z := by
    intro S _ _ z
    rw [← hker S z]
    constructor
    · intro h
      have h1 : (z ≫ q ≫ i) ≫ r = z ≫ q := by simp [hir]
      rw [← h1, h, one_comp_monHom]
    · intro h
      rw [← Category.assoc, h, one_comp_monHom]
  letI : Algebra ℤ_[p] R := (Av.zpLift p R hc).toAlgebra
  obtain ⟨⟨T'⟩, cp, -, -, pt', hpt', -⟩ := hD p C v R hint hp hc P
  have hjm : IsMonHom (q ≫ i) := inferInstance
  obtain ⟨jN, -, hjN, -, hpull⟩ := GlobalTheory.T.torsion_points_isogeny_hopf_order p C v R hint hp A P.A T N pt hpt T' _ pt' hpt'
    (q ≫ i) hjm
  obtain ⟨hK, hid⟩ := GlobalTheory.T.torsion_points_homomorphism_compatible p C v R hint hp A P.A T N pt hpt T' _ pt' hpt' (q ≫ i) hjm K
    hj jN hjN
  obtain ⟨⟨AA, hAA⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hint hp A T N pt hpt
  obtain ⟨⟨AP, hAP⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hint hp P.A T' _ pt' hpt'
  have hinv := GlobalTheory.T.hopf_order_pullback_along_hom p C v R hint hp N AA _ AP jN
    (by rw [hAA, hAP]; exact hpull) (by rw [hAA, hAP]; exact hid)
  rw [hAA, hAP, hK] at hinv
  exact GlobalTheory.T.generation_along_invariants p C R N _ _ _ jN K hinv (gp_polAV hD p C v R hint hp hc P T' _ pt' hpt').1

end GlobalTheory.CompanionTheory.Ar.GR
end
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_torsion_augmentation : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → ∀ (T : TorsRep A p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt → ∀ K : AddSubgroup N, GenAF p (torsFun C T pt) K := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.sub_abelianScheme
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem tors_pts_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : TorsRep G p) (N : Type) [AddCommGroup N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → Finite N := by
  intro R _ _ p G _ T N _ pt h
  haveI := T.free
  haveI := T.fin
  have hx : ∀ x, ∃ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x := fun x =>
    (T.univ R (pt x) ((h.range _).2 ⟨x, rfl⟩)).exists
  choose f hf using hx
  refine Finite.of_injective f fun x y e => h.inj ?_
  rw [← hf x, ← hf y, e]

end GlobalTheory.CompanionTheory.Ar.GR
end
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : TorsRep G p) (N : Type) [AddCommGroup N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → Finite N := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.tors_pts_finite
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem subquotientStatement_of_quotient_zarhin_hodgeTate
    (hQ : QuotientByFiniteFlatStatement) (hZ : ZarhinStatement) (hH : HodgeTateDatumStatement) :
    SubquotientStatement := by
  intro p _ C _ _ _ v R _ _ hv hp hc N _ M hM K
  obtain ⟨A, _, L, hA, hL, hamp, T, N', _, pt, hpt, i, π, hiπ, hst, rfl⟩ := hM
  classical
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : IsCommMonObj A := hA.comm
  haveI : Finite N' := GlobalTheory.T.torsion_points_finite R p A T N' pt hpt
  letI : Fintype N' := Fintype.ofFinite N'
  have hi : Function.Injective i := Function.LeftInverse.injective (g := π) hiπ
  haveI : Finite N := Finite.of_injective i hi
  letI : Fintype N := Fintype.ofFinite N
  obtain ⟨⟨AA, hAA⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hv hp A T N' pt hpt
  have hgen := GlobalTheory.T.abelian_scheme_torsion_augmentation hQ hZ hH p C v R hv hp hc A L hA hL hamp T N' pt hpt (K.map i)
  have hret := GlobalTheory.T.hopf_order_retract_restriction p C v R hv hp N' AA N i π hiπ (by rw [hAA]; exact hst)
  rw [← hAA]
  exact hret.2.2 K (by rw [hAA]; exact hgen)

example : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement →
    SubquotientStatement := subquotientStatement_of_quotient_zarhin_hodgeTate

end GlobalTheory.CompanionTheory.Ar.GR
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_zarhin_hodge_tate_subquotient : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement → SubquotientStatement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate
end
