module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.Guard

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Scheme.{0}}

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

end Lat

section Norm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Comb

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}

theorem exists_comb (hu : ∀ k, IsTanAtG t x (u k)) (cf : Fin m → R) : ∃ w, IsTanAtG t x w ∧ IsCombAtG t x u cf w :=
  ⟨_, isTanAtG_of _ (combT_tan _ (fun j => ovT (hu j)) (fun _ => smT_zero_ovT _) cf),
    (isCombAtG_iff t x (fun j => ovT (hu j)) cf _).2 rfl⟩

theorem comb_unique (hu : ∀ k, IsTanAtG t x (u k)) {cf : Fin m → R} {w w' : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) (h' : IsCombAtG t x u cf w') : w = w' :=
  ((isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 h).symm.trans ((isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 h')

theorem comb_tan (hu : ∀ k, IsTanAtG t x (u k)) {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) : IsTanAtG t x w := by
  obtain ⟨w', h1, h2⟩ := exists_comb hu cf
  exact comb_unique hu h2 h ▸ h1

theorem comb_smul (hu : ∀ k, IsTanAtG t x (u k)) {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) (a : R) : IsCombAtG t x u (fun k => a * cf k) (spMap (epsMul a) ≫ w) := by
  rw [← (isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 h]
  exact (isCombAtG_iff t x (fun j => ovT (hu j)) _ _).2 (by rw [← smT_combT]; rfl)

variable (t x u) in
def Indep : Prop := ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

theorem indep_iff {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (hv : ∀ k, IsTanAtG t x (v k))
    (hi : Indep t x v) (A : Matrix (Fin n) (Fin m) R) (hA : ∀ i, IsCombAtG t x v (fun j => A j i) (u i)) :
    Indep t x u ↔ Function.Injective A.mulVec := by
  have hu := fun i => comb_tan hv (hA i)
  refine ⟨fun h cf cf' e => ?_, fun h cf cf' w h1 h2 => h (hi _ _ w (tanLinG v hv u A cf w hA h1)
    (tanLinG v hv u A cf' w hA h2))⟩
  obtain ⟨w, -, h1⟩ := exists_comb hu cf
  obtain ⟨w', -, h2⟩ := exists_comb hu cf'
  have h3 := comb_unique hv (tanLinG v hv u A cf w hA h1) (e ▸ tanLinG v hv u A cf' w' hA h2)
  exact h cf cf' w h1 (h3 ▸ h2)

theorem indep_of_basis (hu : ∀ k, IsTanAtG t x (u k))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x u cf w) : Indep t x u :=
  fun _ _ w h1 h2 => (hb w (comb_tan hu h1)).unique h1 h2

end Comb

variable {C : Type} [NontriviallyNormedField C] {x : Sp C ⟶ X} {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}

theorem tri_mulVec {K : Type} [Field K] {A : Matrix (Fin m) (Fin m) K} (hA : A.BlockTriangular id) {i : Fin m}
    {cf : Fin m → K} (h : ∀ k, i < k → cf k = 0) :
    (∀ k, i < k → A.mulVec cf k = 0) ∧ A.mulVec cf i = A i i * cf i := by
  have e : ∀ k, A.mulVec cf k = ∑ j, A k j * cf j := fun _ => rfl
  simp only [e]
  refine ⟨fun k hk => Finset.sum_eq_zero fun j _ => ?_, Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)⟩
  · rcases le_or_gt j i with hj | hj
    · rw [hA (show id j < id k from hj.trans_lt hk), zero_mul]
    · rw [h j hj, mul_zero]
  · rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hA (show id j < id i from hj), zero_mul]
    · rw [h j hj, mul_zero]

end Norm

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section AnyBase

variable {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (Ω : Type) [Field Ω]

variable {Z Ω}

end AnyBase

variable (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

variable {Z}

variable {Ω : Type} [Field Ω] {y y' : FlagPt Z Ω} {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Ωˣ} (h : SameFlags y y' d)
  (p : ℕ) [Fact p.Prime] (io : Ω →+* ℂ_[p]) (b : Bool) (hB : b = true → HTBoundSt) (τ : E →+* ℂ)
include h hB

end Pts

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

end GlobalTheory.ShFam.Pad.Guard
