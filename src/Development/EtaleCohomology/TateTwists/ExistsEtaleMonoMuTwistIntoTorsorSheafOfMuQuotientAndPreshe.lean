module

public import Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistIntoTorsorSheafOfMuQuotien
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

theorem kt_mono_sh (q : ℕ) (T G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G)
    (hι : ∀ A, Function.Injective (ι.app A).hom) :
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι)) := by
  have : ∀ U, Mono ((Functor.whiskerLeft Scheme.Γ ι).app U) := fun U =>
    (ModuleCat.mono_iff_injective _).2 (hι _)
  have : Mono (Functor.whiskerLeft Scheme.Γ ι) := NatTrans.mono_of_mono_app _
  infer_instance

theorem kt_res_sec (q : ℕ) (G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (V U : Scheme.{0}) (g : V ⟶ U)
    (x : G.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec (R := ZMod q) G U x) = ofRings.sec (R := ZMod q) G V ((G.map g.appTop).hom x) := by
  unfold Sec.res ofRings.sec ofRings
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ G)).naturality g.op)
  exact this.symm

theorem kt_map_sec (q : ℕ) (T G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G) (U : Scheme.{0})
    (x : T.obj Γ(U, ⊤)) :
    Sec.map ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι))
      (ofRings.sec (R := ZMod q) T U x) = ofRings.sec (R := ZMod q) G U ((ι.app _).hom x) := by
  unfold Sec.map ofRings.sec
  have := congrArg (fun f => (ModuleCat.Hom.hom (NatTrans.app f (op U))) x)
    (toSheafify_naturality Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ ι))
  exact this.symm

def MuTwistQuotientEmbedsInUnitTorsorPresheaf : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    (∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) →
    ∃ (G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G),
      (∀ A, Function.Injective (ι.app A).hom) ∧
      ∃ s : ∀ A : CommRingCat.{0}, Aˣ → G.obj A,
        (∀ (A B : CommRingCat.{0}) (f : A ⟶ B) (v : Aˣ), (G.map f).hom (s A v) = s B (Units.map f.hom.toMonoidHom v)) ∧
        ∀ (A : CommRingCat.{0}) (ζ : Prim q A) (v w : Aˣ), (w : A) = ζ.1 * v →
          s A w = s A v + (ι.app A).hom ((τ.app A).hom (twGenR A ζ))

theorem etale_mu_twist_mono_extends_of_presheaf_torsor_embedding (hpre : MuTwistQuotientEmbedsInUnitTorsorPresheaf) : EtaleMuTwistMonoExtendsToTorsorSheaf := by
  intro q _ T τ hm hl
  obtain ⟨G, ι, hι, s, hs, hr⟩ := hpre q T τ hl
  have hmι := kt_mono_sh q T G ι hι
  refine ⟨ofRings (ZMod q) G, (presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ) ≫
    (presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι), @mono_comp _ _ _ _ _ _ hm _ hmι,
    fun U v => ofRings.sec (R := ZMod q) G U (s _ v), ?_, ?_⟩
  · intro V U g v _
    rw [kt_res_sec]
    exact congrArg _ (hs _ _ g.appTop v)
  · intro U ζ v w h
    beta_reduce
    rw [hr _ ζ v w h]
    rw [show ofRings.sec (R := ZMod q) G U (s _ v + (ι.app _).hom ((τ.app _).hom (twGenR _ ζ))) =
      ofRings.sec (R := ZMod q) G U (s _ v) + ofRings.sec (R := ZMod q) G U ((ι.app _).hom ((τ.app _).hom (twGenR _ ζ))) by
        unfold ofRings.sec
        exact map_add _ _ _]
    congr 1
    exact ((kt_map_sec q T G ι U _).symm.trans (congrArg _ (kt_map_sec q (twF q 1) T τ U (twGenR _ ζ)).symm))

theorem exists_etale_mono_mu_twist_into_torsor_sheaf_of_presheaf (h1 : ExistsEtaleMonoMuTwistKillingRootRelations) (h2 : MuTwistQuotientEmbedsInUnitTorsorPresheaf) :
    EtaleKummerSectionsIntoTwistEmbeddingExist :=
  exists_etale_mono_muTwist_into_torsorSheaf h1 (etale_mu_twist_mono_extends_of_presheaf_torsor_embedding h2)
end LateralTheory.EtaleFoundations
