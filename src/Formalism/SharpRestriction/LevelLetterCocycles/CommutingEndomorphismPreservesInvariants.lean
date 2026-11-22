module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Formalism.SharpRestriction.LevelLetterCocycles.GaloisEquivariantKeyFunction

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section Comm

variable {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W] [Module R W]

end Comm

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section BaseChange

variable {R R' W W' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
  [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] [Module R' W'] [IsScalarTower R R' W']

variable {ι : W →ₗ[R] W'}

variable (hι : IsBaseChange R' ι)

variable {ϖ : R} {ϖ' : R'} {u : R'ˣ} {e : ℕ}

end BaseChange

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section Transfer

variable {O Ok O' Fm : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing Ok] [IsDomain Ok] [IsDiscreteValuationRing Ok] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O Ok] [Algebra Ok O'] [Algebra O O'] [IsScalarTower O Ok O']
  [AddCommGroup Fm] [Module O Fm]

end Transfer

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section More

variable {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W] [Module R W]

end More

end Idx

instance neZero_g (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

instance finite_levelGroup (N : NData D.R D.host D.what₂) : Finite (G0g N) := by
  unfold G0g
  infer_instance

section Lat

open Formalism.IrreducibleCountingLemmas

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {U : Type} [AddCommGroup U]
  [Module R U]

end Lat

section BC

open Formalism.IrreducibleCountingLemmas

variable {O : Type} [CommRing O] [IsDomain O] {W : Type} [AddCommGroup W] [Module O W]
  [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W]

variable {Ok O' : Type} [CommRing Ok] [CommRing O'] [Algebra O Ok] [Algebra O O'] [Algebra Ok O']
  [IsScalarTower O Ok O']

end BC

section Tw

open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt PsiOk)

theorem TwOK_inv {i : X.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ}
    (h : TwOK i k Q ψ) : TwOK i k Q ψ⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hk : (ψ⁻¹).ker = ψ.ker := by
    ext g
    simp [MonoidHom.mem_ker]
  refine ⟨h1, h2, by rw [hk]; exact h3, ?_, ?_, ?_, ?_⟩
  · intro g g' hg
    simp only [MonoidHom.inv_apply]
    rw [h4 g g' hg]
  · intro g
    rw [MonoidHom.inv_apply]
    exact Subgroup.inv_mem _ (h5 g)
  · intro v A hA
    rw [← h6 v A hA]
    simp
  · intro v hv A' hA' σ hσ
    rw [MonoidHom.inv_apply, h7 v hv A' hA' σ hσ, inv_one]

theorem TwOK_psiAt {i : X.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ}
    (b : Bool) (h : TwOK i k Q ψ) : TwOK i k Q (psiAt b ψ) := by
  cases b
  · exact TwOK_inv h
  · exact h

theorem TwOK_of_PsiOk {i : X.Tw} {A Q : Finset (PlE D.host)} {k' : ℕ} {ψ' : X.RCG i Q →* (X.Ok i k')ˣ}
    (h : PsiOk i A Q k' ψ') : TwOK i k' Q (ψ'.comp (X.art i Q)) := by
  classical
  obtain ⟨h1, h2, _, h4, h5, h6, h7, h8⟩ := h
  exact ⟨fun P hP => (h1 P hP).1, (Finset.disjoint_union_right.1 h2).1, h4, h5, h6, h7, h8⟩

end Tw

instance charZero_K (D : Formalism.BasicNotions.D7) (i : D.ntw.Tw) : CharZero (FractionRing (D.ntw.O i)) :=
  (D.nth.iC i).charZero

end Formalism.MainNotions.IntegralHeckeForms

end
