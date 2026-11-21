import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePrisms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExists
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisDividedTaylorExpansionFrobeniusBasis
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K], ∃ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) ∧ (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) ∧ (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) := by
  first | exact @GlobalTheory.TaylorShift.shift_frob_exists | exact GlobalTheory.TaylorShift.shift_frob_exists | (intros; apply GlobalTheory.TaylorShift.shift_frob_exists <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrism_crystal_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  first | exact @GlobalTheory.BKCoord.main | exact GlobalTheory.BKCoord.main | (intros; apply GlobalTheory.BKCoord.main <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  first | exact @GlobalTheory.CrysExt.exists_coord | exact GlobalTheory.CrysExt.exists_coord | (intros; apply GlobalTheory.CrysExt.exists_coord <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_phi_module_map_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  first | exact @GlobalTheory.BKGal.CrysEps.exists_eps | exact GlobalTheory.BKGal.CrysEps.exists_eps | (intros; apply GlobalTheory.BKGal.CrysEps.exists_eps <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysConst

theorem semi_ext {A B C M N : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (k : B →+* C)
    (F G : N →+ C) (hF : ∀ (r : B) y, F (r • y) = k r * F y) (hG : ∀ (r : B) y, G (r • y) = k r * G y)
    (hx : ∀ x, F (u x) = G (u x)) (y : N) : F y = G y := by
  letI : Module B C := Module.compHom C k
  let F' : N →ₗ[B] C := { toFun := F, map_add' := F.map_add, map_smul' := hF }
  let G' : N →ₗ[B] C := { toFun := G, map_add' := G.map_add, map_smul' := hG }
  exact LinearMap.congr_fun (h.hom_ext (w := F') (w' := G') hx) y

theorem semi_lift {A B C M N : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (k : B →+* C)
    (F : M →+ C) (hF : ∀ (r : A) x, F (r • x) = k (f r) * F x) :
    ∃ G : N →+ C, (∀ (r : B) y, G (r • y) = k r * G y) ∧ ∀ x, G (u x) = F x := by
  letI : Module B C := Module.compHom C k
  let F' : M →ₛₗ[f] C := { toFun := F, map_add' := F.map_add, map_smul' := hF }
  obtain ⟨w, hw, -⟩ := h C F'
  exact ⟨w.toAddMonoidHom, fun r y => w.map_smul r y, hw⟩

theorem eq_of_diagonal {l : ℕ} {R C : Type} [CommRing R] [CommRing C] (E : FCrys l R) {P PP S : Obj l R}
    (p₀ p₁ : GlobalTheory.Prism.Hom P PP) (δ : GlobalTheory.Prism.Hom PP S) (hδ : δ.comp p₀ = δ.comp p₁) (k : S.A →+* C)
    (F G : E.M PP →+ C) (hF : ∀ (r : PP.A) y, F (r • y) = k (δ.f r) * F y)
    (hG : ∀ (r : PP.A) y, G (r • y) = k (δ.f r) * G y)
    (hx : ∀ x, F (E.tr p₀ x) = G (E.tr p₁ x)) (y : E.M PP) : F y = G y := by
  obtain ⟨μ, hμ, hμx⟩ := semi_lift (E.tr_bc (δ.comp p₀)) k (F.comp (E.tr p₀).toAddMonoidHom) (fun r x => by
    change F (E.tr p₀ (r • x)) = k (δ.f (p₀.f r)) * F (E.tr p₀ x)
    rw [LinearMap.map_smulₛₗ, hF])
  have hν : ∀ (r : PP.A) y, (μ.comp (E.tr δ).toAddMonoidHom) (r • y) =
      (k.comp δ.f) r * (μ.comp (E.tr δ).toAddMonoidHom) y := fun r y => by
    change μ (E.tr δ (r • y)) = k (δ.f r) * μ (E.tr δ y)
    rw [LinearMap.map_smulₛₗ, hμ]
  have h0 := semi_ext (E.tr_bc p₀) (k.comp δ.f) F _ hF hν (fun x => by
    change _ = μ (E.tr δ (E.tr p₀ x))
    rw [← E.tr_comp, hμx]; rfl) y
  have h1 := semi_ext (E.tr_bc p₁) (k.comp δ.f) G _ hG hν (fun x => by
    change _ = μ (E.tr δ (E.tr p₁ x))
    rw [← E.tr_comp, ← hx]
    have : ∀ q : GlobalTheory.Prism.Hom P S, δ.comp p₀ = q → μ (E.tr q x) = F (E.tr p₀ x) := by
      rintro _ rfl
      exact hμx x
    exact (this _ hδ).symm) y
  exact h0.trans h1.symm

theorem constantCoeff_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∀ y τ i, PowerSeries.constantCoeff (lam₀ y τ i) = PowerSeries.constantCoeff (lam₁ y τ i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ EE c _ sh hsh PP S₀ p₀ p₁ δ j j₀ hδ hj _ lam₀ lam₁ h₀ h₁ hx₀ hx₁
    y τ i
  have hc : ∀ f : K⟦X⟧, PowerSeries.constantCoeff (sh f) = f := fun f => by
    simpa using hsh f 0
  let pr : (ZMod a → ι → K⟦X⟧⟦X⟧) →+ K⟦X⟧ :=
    { toFun := fun q => PowerSeries.constantCoeff (q τ i)
      map_zero' := by simp
      map_add' := fun q q' => by simp }
  refine eq_of_diagonal EE p₀ p₁ δ hδ (j₀ τ) (pr.comp lam₀) (pr.comp lam₁) (fun r y => ?_) (fun r y => ?_)
    (fun x => ?_) y
  · change PowerSeries.constantCoeff (lam₀ (r • y) τ i) = _ * PowerSeries.constantCoeff (lam₀ y τ i)
    rw [h₀, map_mul, hj]
  · change PowerSeries.constantCoeff (lam₁ (r • y) τ i) = _ * PowerSeries.constantCoeff (lam₁ y τ i)
    rw [h₁, map_mul, hj]
  · change PowerSeries.constantCoeff (lam₀ (EE.tr p₀ x) τ i) = PowerSeries.constantCoeff (lam₁ (EE.tr p₁ x) τ i)
    rw [hx₀, hx₁, hc, PowerSeries.constantCoeff_C]

end GlobalTheory.CrysConst
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_coordinates_constantCoeff_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∀ y τ i, PowerSeries.constantCoeff (lam₀ y τ i) = PowerSeries.constantCoeff (lam₁ y τ i) := by
  atlas_forward_decl GlobalTheory.CrysConst.constantCoeff_eq
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  first | exact @GlobalTheory.CrysFrobCoord.frob_in_coordinates | exact GlobalTheory.CrysFrobCoord.frob_in_coordinates | (intros; apply GlobalTheory.CrysFrobCoord.frob_in_coordinates <;> assumption)
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CrysInteg

theorem mem_of_semiBC {A B M N Q : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup Q] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (g : N →+ Q) (H : AddSubgroup Q) (hg : ∀ (r : B) (x : M), g (r • u x) ∈ H) (y : N) : g y ∈ H := by
  have hspan : y ∈ Submodule.span B (Set.range u) := by
    have h1 : (Submodule.span B (Set.range u)).mkQ = 0 := h.hom_ext fun x => by
      rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩
    have := LinearMap.congr_fun h1 y
    rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have key : ∀ z ∈ Submodule.span B (Set.range u), ∀ r : B, g (r • z) ∈ H := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact fun r => hg r x
    | zero =>
      intro r
      rw [smul_zero, map_zero]
      exact H.zero_mem
    | add z w _ _ hz hw =>
      intro r
      rw [smul_add, map_add]
      exact add_mem (hz r) (hw r)
    | smul s z _ hz =>
      intro r
      rw [smul_smul]
      exact hz _
  have := key y hspan 1
  rwa [one_smul] at this

def divSub {R σ ι : Type} [CommRing R] (S : Subring R) (τ : σ) (i : ι) (k : ℕ) :
    AddSubgroup (σ → ι → R⟦X⟧) where
  carrier := {v | (k.factorial : R) * coeff k (v τ i) ∈ S}
  add_mem' {v w} hv hw := by
    change (k.factorial : R) * coeff k (v τ i + w τ i) ∈ S
    rw [map_add, mul_add]
    exact add_mem hv hw
  zero_mem' := by
    change (k.factorial : R) * coeff k (0 : R⟦X⟧) ∈ S
    rw [map_zero, mul_zero]
    exact zero_mem _
  neg_mem' {v} hv := by
    change (k.factorial : R) * coeff k (-(v τ i)) ∈ S
    rw [map_neg, mul_neg]
    exact neg_mem hv

theorem factorial_mul_coeff_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ x, c x ∈ P.M) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (J τ y) ∈ S O K e) → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → ∀ y τ i (k : ℕ), (k.factorial : K⟦X⟧) * coeff k (lam y τ i) ∈ S O K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hc PP p J hJ lam hsm htr y τ i k
  refine mem_of_semiBC (EE.tr_bc p) lam (divSub (S O K e).toSubring τ i k) (fun r x => ?_) y
  change (k.factorial : K⟦X⟧) * coeff k (lam (r • EE.tr p x) τ i) ∈ S O K e
  rw [hsm, htr, PowerSeries.coeff_mul_C, ← mul_assoc]
  exact mul_mem (hJ τ r k) (A_le_S l e (frob_mem_A l (mem_tot.1 (hc x) (τ - 1) i)))

end GlobalTheory.BKGal.CrysInteg
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorial_mul_crystalCoord_coeff_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ x, c x ∈ P.M) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (J τ y) ∈ S O K e) → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → ∀ y τ i (k : ℕ), (k.factorial : K⟦X⟧) * coeff k (lam y τ i) ∈ S O K e := by
  atlas_forward_decl GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysStrat

theorem single_mem_M {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (σ : ZMod a) (j : ι) :
    (Pi.single σ (Pi.single j (1 : K⟦X⟧)) : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  by_cases h : τ = σ
  · subst h; rw [Pi.single_eq_same]
    by_cases h' : i = j
    · subst h'; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h']; exact zero_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem mulVec_single_one' {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (j i : ι) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_stratification : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I hBK sh φ₂ hsh hφC hφsh
  obtain ⟨EE, c, hinj, hcM, hsurj, hsemi, hO, hfr⟩ := GlobalTheory.T.breuilKisinPrism_crystal_coordinates l a e _ _ (thetaW a LL) ϖ ι P _ _ hBS hBK
  obtain ⟨PP, S₀, p₀, p₁, δ, j, j₀, hI, hδ, hj₀, hjp, hjφ, hS, hS', -⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ hl sh φ₂ hsh hφC hφsh
  obtain ⟨lam₀, hl₀, hv₀⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₀ j PowerSeries.C
    (fun τ w => (hjp τ w).1)
  obtain ⟨lam₁, hl₁, hv₁⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₁ j sh
    (fun τ w => (hjp τ w).2)
  obtain ⟨ε, hε⟩ := GlobalTheory.T.crystalline_phi_module_map_exists l a e _ _ (thetaW a LL) ϖ ι P EE c hinj hcM hsurj hsemi hO sh hsh PP p₀ p₁ j hjp
    lam₀ lam₁ hl₀ hl₁ hv₀ hv₁
  have hsh0 : ∀ f, PowerSeries.constantCoeff (sh f) = f := fun f => by
    simpa using hsh f 0

  have hcol : ∀ (τ : ZMod a) (jj : ι), ∃ x, c x = Pi.single (τ - 1) (Pi.single jj 1) :=
    fun τ jj => hsurj _ (single_mem_M P _ jj)
  have hv1 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      lam₁ (EE.tr p₁ x) τ = Pi.single jj 1 := fun τ jj x hx => funext fun i => by
    rw [hv₁, hx, Pi.single_eq_same]
    by_cases h : i = jj
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hv0 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      ∀ i, lam₀ (EE.tr p₁ x) τ i = ε τ i jj := fun τ jj x hx i => by
    rw [hε, hv1 τ jj x hx, mulVec_single_one']
  have hlK : (l : ↥LL.1) ≠ 0 := by
    have h := (map_ne_zero (algebraMap ℚ_[l] ↥LL.1)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
    rwa [map_natCast] at h
  have hl0 : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ≠ 0 := fun h => hlK (by
    have := congrArg (fun f => PowerSeries.constantCoeff (PowerSeries.constantCoeff f)) h
    simpa using this)
  refine ⟨ε, fun τ => ?_, fun τ => ?_, fun τ i jj k => ?_⟩
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol τ jj
    rw [Matrix.map_apply, ← hv0 τ jj x hx i,
      GlobalTheory.T.crystal_coordinates_constantCoeff_eq l a e _ _ (thetaW a LL) ϖ ι EE c hsemi sh hsh PP S₀ p₀ p₁ δ j j₀ hδ hj₀ hjp lam₀ lam₁ hl₀ hl₁ hv₀ hv₁,
      hv1 τ jj x hx, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol (τ - 1) jj
    have hlI : ((l : ℕ) : PP.A) ∈ PP.I := by rw [hI]; exact Ideal.mem_span_singleton_self _
    obtain ⟨n, k, hn⟩ := exists_isFrac ((l : ℕ) : PP.A) (EE.Φ PP ⟨_, hlI⟩ (EE.tr p₁ x))
    have G₀ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₀ j PowerSeries.C φ₂
      (fun τ w => (hjp τ w).1) hjφ hφC (PowerSeries.C_injective) lam₀ hl₀ hv₀ _ n k hn τ i
    have G₁ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₁ j sh φ₂
      (fun τ w => (hjp τ w).2) hjφ hφsh (fun f g h => by rw [← hsh0 f, ← hsh0 g, h]) lam₁ hl₁ hv₁ _ n k hn
    have hy1 := hv1 (τ - 1) jj x hx
    have hy0 : ∀ m, lam₀ (EE.tr p₁ x) (τ - 1) m = ε (τ - 1) m jj := hv0 (τ - 1) jj x hx
    have hE := congrFun (hε n τ) i
    rw [G₀] at hE
    simp only [Matrix.mulVec, dotProduct, G₁, hy1, hy0] at hE
    have key : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k *
        (((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) i jj =
        ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k * (ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh) i jj := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have h1 : ∀ q, φ₂ ((Pi.single jj (1 : (↥LL.1)⟦X⟧⟦X⟧) : ι → (↥LL.1)⟦X⟧⟦X⟧) q) =
          (Pi.single jj 1 : ι → (↥LL.1)⟦X⟧⟦X⟧) q := fun q => by
        by_cases h : q = jj
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      simp only [h1] at hE
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true] at hE
      simp only [Matrix.map_apply] at hE ⊢
      rw [hE, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    exact (mul_left_cancel₀ (pow_ne_zero k hl0) key).symm
  · obtain ⟨x, hx⟩ := hcol τ jj
    rw [← hv0 τ jj x hx i]
    exact GlobalTheory.T.factorial_mul_crystalCoord_coeff_mem l a e _ _ (thetaW a LL) ϖ ι P EE c hcM PP p₀ j hS' lam₀ hl₀ hv₀ _ τ i k

end GlobalTheory.CrysStrat
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_crystal_stratification_matrix : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  atlas_forward_decl GlobalTheory.CrysStrat.exists_stratification
end

section
section
theorem GlobalTheory.cauchy_product_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  intro R _ x α β A B hA hB r
  obtain ⟨NA, hNA⟩ := hA r
  obtain ⟨NB, hNB⟩ := hB r
  have hα : ∀ p ≥ NA, x ^ r ∣ α p := by
    intro p hp
    have h1 := hNA p hp
    have h2 := hNA (p + 1) (by omega)
    have e : α p = (A - ∑ i ∈ Finset.range p, α i) - (A - ∑ i ∈ Finset.range (p + 1), α i) := by
      rw [Finset.sum_range_succ]; ring
    rw [e]; exact dvd_sub h1 h2
  refine ⟨NA + NB, fun n hn => ?_⟩
  have key : ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = ∑ p ∈ Finset.range n, α p * ∑ q ∈ Finset.range (n - p), β q := by
    rw [Finset.sum_range_diag_flip n (fun p q => α p * β q)]
    simp only [Finset.mul_sum]
  have hsplit : A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = (A - ∑ p ∈ Finset.range n, α p) * B
        + ∑ p ∈ Finset.range n, α p * (B - ∑ q ∈ Finset.range (n - p), β q) := by
    rw [key, Finset.sum_congr rfl (fun p _ => mul_sub (α p) B _), Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    ring
  rw [hsplit]
  refine dvd_add (dvd_mul_of_dvd_left (hNA n (by omega)) _) (Finset.dvd_sum fun p _ => ?_)
  by_cases hp' : NA ≤ p
  · exact dvd_mul_of_dvd_left (hα p hp') _
  · exact dvd_mul_of_dvd_right (hNB _ (by omega)) _
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchy_product_partial_sums_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  atlas_forward_decl GlobalTheory.cauchy_product_dvd_pow
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.DescFalling

theorem desc_eq_X_pow_smul_nabla_pow {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι) :
    C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  have hX : ∀ w, C.nabla ((X : K⟦X⟧) • w) = w + (X : K⟦X⟧) • C.nabla w := fun w => by
    have h := C.leibniz (fun _ => X) w
    have e1 : ∀ u : Vec K a ι, ((fun _ => (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • u = (X : K⟦X⟧) • u :=
      fun u => rfl
    have e2 : ((fun _ => PowerSeries.derivative K (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • w = w := by
      simp only [PowerSeries.derivative_X]
      exact one_smul _ w
    rw [e1, e1, e2] at h
    exact h
  have hcomm : ∀ (j : ℕ) (w : Vec K a ι),
      (C.nabla ^ j) ((X : K⟦X⟧) • C.nabla w) = (X : K⟦X⟧) • (C.nabla ^ (j + 1)) w + j • (C.nabla ^ j) w := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih, map_add, hX, map_nsmul, pow_succ' C.nabla (j + 1),
        Module.End.mul_apply, pow_succ' C.nabla j, Module.End.mul_apply, succ_nsmul]
      abel
  induction k generalizing v with
  | zero => simp [Conn.desc_zero]
  | succ k ih =>
    rw [Conn.desc_succ, ih, Conn.N_apply, map_sub, hcomm, map_nsmul, add_sub_cancel_right, smul_smul,
      ← pow_succ]

end GlobalTheory.DescFalling
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.desc_eq_X_pow_smul_nabla_pow' : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι), C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  atlas_forward_decl GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal.Conn

theorem pow_apply_smul_nsmul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      k.choose p • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_choose_succ_nsmul (fun i j => (fun τ => (⇑(derivative K))^[i] (f τ)) • (C.nabla ^ j) v) k,
      pow_succ', Module.End.mul_apply, ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
    rw [map_nsmul, C.leibniz, smul_add, add_comm]
    congr 2
    · rw [show k + 1 - p = k - p + 1 by omega, pow_succ', Module.End.mul_apply]
    · congr 1
      funext τ
      rw [Function.iterate_succ_apply']

theorem pow_apply_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  rw [pow_apply_smul_nsmul]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm

end GlobalTheory.BKReal.Conn
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nabla_pow_apply_smul_leibniz : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι), (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  atlas_forward_decl GlobalTheory.BKReal.Conn.pow_apply_smul
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal

theorem coeff_iterate_derivative_descFactorial (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) (m : ℕ) :
    coeff m ((⇑(derivative K))^[p] f) = ((m + p).descFactorial p : K) * coeff (m + p) f := by
  induction p generalizing m with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', coeff_derivative, ih, Nat.descFactorial_succ,
      show m + 1 + p = m + (p + 1) by omega, show m + (p + 1) - p = m + 1 by omega]
    push_cast
    ring

theorem descN_eq_X_pow_mul_iterate_derivative :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧), descN K p f = X ^ p * (⇑(derivative K))^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative_descFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega), Nat.cast_zero, zero_mul]

end GlobalTheory.BKReal
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' : ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧), descN K p f = X ^ p * (⇑(derivative K))^[p] f := by
  atlas_forward_decl GlobalTheory.BKReal.descN_eq_X_pow_mul_iterate_derivative
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TaylorBasis

theorem cauchy_dvd {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R)
    (hA : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p)
    (hB : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) :=
  GlobalTheory.T.cauchy_product_partial_sums_dvd_pow x α β A B hA hB r

theorem desc_eq {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (v : Vec K a ι) : C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v :=
  GlobalTheory.T.desc_eq_X_pow_smul_nabla_pow' C k v

theorem nabla_pow_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (f : ZMod a → K⟦X⟧) (v : Vec K a ι) : (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) :=
  GlobalTheory.T.nabla_pow_apply_smul_leibniz C k f v

theorem descN_eq (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) :
    descN K p f = X ^ p * (⇑(derivative K))^[p] f :=
  GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' K p f

theorem muDiv_mul_choose {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {k p : ℕ} (h : p ≤ k) :
    ϖ.muDiv a O g k * (k.choose p : OCr l O) = ϖ.muDiv a O g p * ϖ.muDiv a O g (k - p) := by
  have hx := ϖ.theta_mu (ϖ.gal_pi a g)
  have key : dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) = dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p) := by
    apply sub_eq_zero.1
    refine acris_nat_cancel (Nat.factorial_ne_zero k) ?_
    have hf : (k.factorial : Per.Acris l) = (k.choose p : Per.Acris l) * p.factorial * (k - p).factorial := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial h]
    rw [show (k.factorial : Per.Acris l) * (dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) -
        dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p)) = (k.choose p : Per.Acris l) * ((k.factorial : Per.Acris l) *
        dpow (ϖ.mu g) hx k) - (k.choose p : Per.Acris l) * (((p.factorial : Per.Acris l) * dpow (ϖ.mu g) hx p) *
        (((k - p).factorial : Per.Acris l) * dpow (ϖ.mu g) hx (k - p))) by
      linear_combination (-(dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p))) * hf]
    rw [factorial_mul_dpow, factorial_mul_dpow, factorial_mul_dpow, ← pow_add, Nat.add_sub_cancel' h, sub_self]
  have hm : ∀ n, ϖ.muDiv a O g n =
      (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) (dpow (ϖ.mu g) hx n) := fun n => rfl
  rw [hm, hm, hm, ← map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O), ← map_mul,
    ← map_mul, key]

theorem galOCr_iC_taylor {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) (c : ZMod a → S O K e) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ galOCr O (g : GQ l) (ϖ.iC t K c) -
      ∑ p ∈ Finset.range n, ϖ.muDiv a O g p * ϖ.iC t K (fun τ => ⟨descN K p (c τ), descN_mem_S e p (c τ).2⟩) := by
  choose N hN using fun τ : ZMod a => ϖ.taylor_S a O K g (c τ) r
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun τ => hN τ n ((Finset.le_sup (Finset.mem_univ τ)).trans hn)
  refine ⟨∑ τ, idem (constC t) τ * z τ, ?_⟩
  simp only [PiSys.iC, glue_apply, map_sum, map_mul, galOCr_idem, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_left_comm, ← hz τ, mul_sub, Finset.mul_sum]
  simp only [mul_left_comm (idem (constC t) τ)]

theorem coord_desc {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (m : Vec K a ι) (k : ℕ) (τ : ZMod a) (i : ι) :
    (P.mxInv τ *ᵥ C.desc k m τ) i = ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) *
      (descN K p ((P.mxInv τ *ᵥ m τ) j) * (X ^ (k - p) * (P.mxInv τ *ᵥ (C.nabla ^ (k - p)) (P.phi (bas j)) τ) i)) := by
  have hΦ : ∀ (f : ZMod a → K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (f • w) τ) i = f τ * (P.mxInv τ *ᵥ w τ) i := fun f w => by
    rw [Pi.smul_apply', Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦs : ∀ (s : K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (s • w) τ) i = s * (P.mxInv τ *ᵥ w τ) i := fun s w => by
    rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦsum : ∀ {J : Type} (s : Finset J) (w : J → Vec K a ι),
      (P.mxInv τ *ᵥ (∑ x ∈ s, w x) τ) i = ∑ x ∈ s, (P.mxInv τ *ᵥ w x τ) i := fun s w => by
    rw [Finset.sum_apply, Matrix.mulVec_sum, Finset.sum_apply]
  conv_lhs => rw [desc_eq, P.eq_sum_phi_bas m]
  rw [hΦs, map_sum, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nabla_pow_smul, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
  rw [hΦs, hΦ, descN_eq]
  have hX : (X : K⟦X⟧) ^ k = X ^ p * X ^ (k - p) := by rw [← pow_add, Nat.add_sub_cancel' hpk]
  rw [hX]
  ring

theorem taylor_of_basis {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type}
    [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (C : Conn P)
    (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι),
      (X : K⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S O K e)
    (hΓ : ∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (l : OCr l O) ^ r ∣ toOCr l O (Γ i j) -
        ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ j k i⟩)) :
    I.Taylor C := by
  intro g
  obtain ⟨Γ, hΓL, hconv⟩ := hΓ g
  refine ⟨Γ, hΓL, fun m r => ?_⟩
  let c : ι → ZMod a → ↥(S O K e) := coordL P (S O K e) m
  have hcj : ∀ j τ, (c j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m : Vec K a ι) τ) j := fun j τ => rfl
  have hcm : ∀ j, toCris t ϖ P m j = ϖ.iC t K (c j) := fun j => rfl
  have F3 : ∀ k i, toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩ i =
      ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : OCr l O) *
        (ϖ.iC t K (fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) *
          ϖ.iC t K (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
    intro k i
    have h1 : coordL P (S O K e) ⟨C.desc k m, C.desc_mem k m.2⟩ i =
        ∑ j, ∑ p ∈ Finset.range (k + 1), ((k.choose p : ℕ) : ZMod a → ↥(S O K e)) *
          ((fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) * (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
      funext τ
      apply Subtype.ext
      refine (coord_desc C m k τ i).trans ?_
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, AddSubmonoidClass.coe_finset_sum,
        MulMemClass.coe_mul, SubringClass.coe_natCast, hcj]
    rw [toCris_apply, h1]
    simp only [map_sum, map_mul, map_natCast]
  have key : ∀ p : ι × ι, ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      galOCr O (g : GQ l) (ϖ.iC t K (c p.2)) * toOCr l O (Γ p.1 p.2) -
        ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c p.2 τ), descN_mem_S e q (c p.2 τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 (k - q) p.1⟩)) :=
    fun p => cauchy_dvd _ _ (fun k => ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 k p.1⟩)) _ _
      (fun r => galOCr_iC_taylor t ϖ g (c p.2) r) (fun r => hconv p.1 p.2 r) r
  choose N hN using key
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun p : ι × ι => hN p n ((Finset.le_sup (Finset.mem_univ p)).trans hn)
  refine ⟨fun i => ∑ j, z (i, j), funext fun i => ?_⟩
  have e1 : (Γ.map (toOCr l O) *ᵥ fun j => galOCr O (g : GQ l) (toCris t ϖ P m j)) i =
      ∑ j, galOCr O (g : GQ l) (ϖ.iC t K (c j)) * toOCr l O (Γ i j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hcm]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : (∑ k ∈ Finset.range n, ϖ.muDiv a O g k • toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩) i =
      ∑ j, ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c j τ), descN_mem_S e q (c j τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ j (k - q) i⟩)) := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, F3, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
    rw [← mul_assoc, muDiv_mul_choose a O ϖ g (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))]
    ring
  rw [Pi.sub_apply, e1, e2, ← Finset.sum_sub_distrib, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => hz (i, j)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : Lat a ↥(OL LL) ↥LL.1 ϖ) (I : Ident (thetaW a LL) ϖ P T) (C : Conn P) (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e), (∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩)) → I.Taylor C :=
  fun _ _ _ _ _ _ ϖ LL _ _ _ _ _ _ _ _ I C hS hΓ => taylor_of_basis (thetaW _ LL) ϖ I C hS hΓ

end GlobalTheory.TaylorBasis
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_taylor_formula_breuilKisin_lattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : Lat a ↥(OL LL) ↥LL.1 ϖ) (I : Ident (thetaW a LL) ϖ P T) (C : Conn P) (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e), (∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩)) → I.Taylor C := by
  atlas_forward_decl GlobalTheory.TaylorBasis.main
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.IntConnTaylor

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∃ C : Conn P, C.nabla = P.nabla ∧ Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK
  obtain ⟨sh, φ₂, h1, h2, h3⟩ := GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible l (↥LL.1)
  obtain ⟨ε, hε0, hεφ, hεS⟩ := GlobalTheory.T.exists_integral_crystal_stratification_matrix hBS l a e ϖ LL hl2 ι P T I hBK sh φ₂ h1 h2 h3
  have hc := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow (↥(OL LL)) (↥LL.1) l e a ι P sh φ₂ h1 h2 h3 ε hε0 hεφ
  have hphi : ∀ j, P.phi (bas j) ∈ P.MM := fun j =>
    P.ext_mono (fun _ h => A_le_S l e h) (P.phi_mem_L (P.bas_mem_M j))
  have hpow : ∀ (n : ℕ) (j : ι), (P.nabla ^ n) (P.phi (bas j)) ∈ P.MM := fun n j =>
    mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => by rw [← hc τ n i j]; exact hεS τ i j n
  have hMM : ∀ m ∈ P.MM, P.nabla m ∈ P.MM := fun m hm =>
    P.nabla_mem_MM_of_basis (fun j => by simpa using hpow 1 j) hphi hm
  let C : Conn P := ⟨P.nabla, fun f v => P.nabla_smul_tot f v, hMM⟩
  have hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k *
      (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e := fun τ j k i =>
    mul_mem (pow_mem (uIn (S (↥(OL LL)) (↥LL.1) e)).2 k)
      (P.mem_extc_iff.1 (mem_tot.1 (hpow k j) τ) i)
  exact ⟨C, rfl, GlobalTheory.T.galois_taylor_formula_breuilKisin_lattice l a e ϖ LL hl2 ι P _ _ C hS (GlobalTheory.T.galois_dividedTaylor_expansion_frobeniusBasis hBS l a e ϖ LL hl2 ι P T I hBK hS)⟩

end GlobalTheory.IntConnTaylor
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralConnection_taylorFormula_tameBreuilKisin : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∃ C : Conn P, C.nabla = P.nabla ∧ Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C := by
  atlas_forward_decl GlobalTheory.IntConnTaylor.main
end
