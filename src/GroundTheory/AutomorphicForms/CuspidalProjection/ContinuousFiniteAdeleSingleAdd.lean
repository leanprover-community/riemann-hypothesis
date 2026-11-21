import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.CuspidalProjection.Unfold
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

open MeasureTheory Set Function Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalProjection

open Reduction AutomorphicForm CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ} (v : HeightOneSpectrum (𝓞 K))

theorem continuous_finiteAdeleSingleAdd :
    Continuous (GroundTheory.Global.finiteAdeleSingleAdd (K := K) v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 {v}ᶜ := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact Set.finite_singleton v
  let g : v.adicCompletion K → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (𝓟 {v}ᶜ) := fun x =>
    ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x,
      Filter.eventually_principal.2 fun w hw => by
        rw [Pi.single_eq_of_ne (Set.mem_compl_singleton_iff.1 hw)]
        exact zero_mem _⟩
  have hs : Continuous fun x : v.adicCompletion K =>
      Pi.single (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x :=
    continuous_single v
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.2 hs
  have heq : (GroundTheory.Global.finiteAdeleSingleAdd (K := K) v : v.adicCompletion K → _) =
      RestrictedProduct.inclusion _ _ hle ∘ g := by
    funext x
    rfl
  rw [heq]
  exact (RestrictedProduct.continuous_inclusion hle).comp hg

def adeleSingle : v.adicCompletion K →+ 𝔸[K] :=
  (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
    (GroundTheory.Global.finiteAdeleSingleAdd v)


def evAt : 𝔸[K] →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) v).comp
    (RingHom.snd _ _)

theorem evAt_apply (x : 𝔸[K]) : evAt v x = x.2 v := rfl


def compAt : AdelicGLn.AdelicGL K n →* GL (Fin n) (v.adicCompletion K) :=
  (RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 K) => GL (Fin n) (w.adicCompletion K)) v).comp
    ((MonoidHom.snd _ _).comp (AdelicGLn.restrictedProductEquiv K n).toMonoidHom)

theorem compAt_apply (g : AdelicGLn.AdelicGL K n) (a b : Fin n) :
    (compAt v g : GL (Fin n) (v.adicCompletion K)) a b = ((g : AdelicGLn.AdelicMatrix K n) a b).2 v :=
  AdelicGLn.restrictedProductEquiv_apply_snd K n g v a b

theorem continuous_compAt : Continuous (compAt (K := K) (n := n) v) :=
  (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (AdelicGLn.restrictedProductEquiv K n).continuous)

def awayAt : 𝔸[K] →+*
    InfiniteAdeleRing K × ((w : {w : HeightOneSpectrum (𝓞 K) // w ≠ v}) → w.1.adicCompletion K) :=
  (RingHom.fst _ _).prod (RingHom.pi fun w =>
    (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) w.1).comp
      (RingHom.snd _ _))

def AgreeAway (g g' : AdelicGLn.AdelicGL K n) : Prop :=
  (awayAt v).mapMatrix (g : AdelicGLn.AdelicMatrix K n) =
    (awayAt v).mapMatrix (g' : AdelicGLn.AdelicMatrix K n)

variable (n r) in

def unipAt (y : UPos n r → v.adicCompletion K) : normOneGL K n :=
  unipOne K n r fun p => adeleSingle v (y p)

theorem unipAt_add (y y' : UPos n r → v.adicCompletion K) :
    unipAt n r v (y + y') = unipAt n r v y * unipAt n r v y' := by
  rw [unipAt, unipAt, unipAt, ← unipOne_add]
  congr 1
  funext p
  simp [map_add]



def unipCoord (g : normOneGL K n) : UPos n r → v.adicCompletion K := fun p =>
  (compAt v (g : AdelicGLn.AdelicGL K n) : GL (Fin n) (v.adicCompletion K)) p.1.1 p.1.2

theorem continuous_unipCoord : Continuous (unipCoord (K := K) (n := n) (r := r) v) := by
  refine continuous_pi fun p => ?_
  have h : Continuous fun g : GL (Fin n) (v.adicCompletion K) =>
      (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) p.1.1 p.1.2 :=
    Units.continuous_val.matrix_elem p.1.1 p.1.2
  exact h.comp ((continuous_compAt v).comp continuous_subtype_val)



end CuspidalProjection

end

end GroundTheory.Automorphic
