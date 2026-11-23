module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsOfInjectiveZmodEtaleSheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.TwResExt

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (f : F ⟶ G) (g : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem twRes_ext : ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧
    (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
    IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧
    ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u') := by
  intro q _ i
  obtain ⟨hKI, hInj, hGE, hQI, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  refine ⟨⟨hGE, resAug _, hQI, fun _ _ => rfl⟩, fun t => ?_, ?_⟩
  · haveI := hInj t
    exact (GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf q ((res _ (tw q i)).X t)).2
  intro T e ⟨_, ε, hε, he⟩
  have hext := GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) (tw q i) T (res _ (tw q i)) ε
  refine ⟨?_, fun u u' huu => ?_⟩
  · obtain ⟨m, hm⟩ := hext.1 (resAug _)
    refine ⟨m, fun U ζ => ?_⟩
    rw [← he U ζ, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]
    rfl
  · refine hext.2 u u' ?_
    have htw := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2
    obtain ⟨hres, hrel, huniq⟩ := htw
    let ψ : (T ⟶ res _ (tw q i)) → (tw q i ⟶ (res _ (tw q i)).X 0) := fun v => sglι (tw q i) ≫ (ε ≫ v).f 0
    have key : ∀ v : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (ψ v) (twGen i ζ) = Sec.map (v.f 0) (e U ζ) := by
      intro v U ζ
      rw [← he U ζ]
      rfl
    have hnat : ∀ v : T ⟶ res _ (tw q i), ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
        Sec.res g (Sec.map (ψ v) (twGen i ζ)) = Sec.map (ψ v) (twGen i (ζ.map g.appTop.hom)) := by
      intro v V U g ζ
      rw [← hres V U g ζ]
      exact (congrArg (fun f => f.hom (twGen i ζ)) ((ψ v).hom.naturality g.op)).symm
    have hrl : ∀ v : T ⟶ res _ (tw q i), ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ),
        ξ.1 = ζ.1 ^ (a : ZMod q).val →
        Sec.map (ψ v) (twGen i ξ) = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • Sec.map (ψ v) (twGen i ζ) := by
      intro v U ζ ξ a h
      rw [hrel U ζ ξ a h]
      exact map_nsmul _ _ _
    obtain ⟨φ, -, hφ⟩ := huniq ((res _ (tw q i)).X 0) (fun U ζ => Sec.map (ψ u) (twGen i ζ)) (hnat u) (hrl u)
    have h1 := hφ (ψ u) fun U ζ => rfl
    have h2 := hφ (ψ u') fun U ζ => by rw [key, key, huu]
    have h12 : ψ u = ψ u' := h2.symm ▸ h1 ▸ rfl
    apply HomologicalComplex.from_single_hom_ext
    exact (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)) _ _).1 h12

end GlobalTheory.EtC.TwResExt
