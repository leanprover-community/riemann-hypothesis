module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantSpecLocalRingConstBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCyclotomicPrimitiveRootsOfStrictlyHenselStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSectionStatement
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sh_eqv_tw : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  intro q i A B _ _ φ hA hB hq
  obtain ⟨hAl, _⟩ := hA
  obtain ⟨hBl, _⟩ := hB
  obtain ⟨ζ⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A ⟨hAl, ‹_›⟩ hq
  let S : Scheme.{0} := Spec (CommRingCat.of A)
  let ζS : Prim q Γ(S, ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ζ
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i S ζS
  have hac : ∀ (C : Type) [CommRing C], SH C → AcycF (ZMod q) (sch.obj (Spec (CommRingCat.of C))) (tw q i) :=
    fun C _ hC n hn => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) C hC (tw q i) n hn
  refine GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) S (twGen i ζS) hgen S (Spec (CommRingCat.of B)) (𝟙 S)
    (Spec.map (CommRingCat.ofHom φ)) (hac A ⟨hAl, ‹_›⟩) (hac B ⟨hBl, ‹_›⟩) ?_
  have cA := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) A
  have cB := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) B
  have hcomp : (fun φ' : LocallyConstant S (ZMod q) => φ'.comap (Spec.map (CommRingCat.ofHom φ)).base.hom) ∘
      (fun c : ZMod q => LocallyConstant.const S c) = fun c => LocallyConstant.const _ c := by
    funext c; ext x; rfl
  refine (Function.Bijective.of_comp_iff _ cA).1 ?_
  rw [hcomp]
  exact cB
end GlobalTheory.EtC
