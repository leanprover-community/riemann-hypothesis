module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateTwistMulDegreeZeroHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorOfCompatIsIsoTargetStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorUniversalPropertyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroTensorOfDegreeZeroComplexesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistGeneratorTmulOrderLocallyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallyInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallySurjectiveStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TwMul

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem secMap_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem tw_mul_isTensor : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ) := by
  intro q _ i j k hk
  obtain ⟨K, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (sgl (tw q i)) (sgl (tw q j))
  have hzK : ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) :=
    GlobalTheory.T.isZero_tensor_of_degree_zero_complexes (ZMod q) τ hτ (fun s hs => HomologicalComplex.isZero_single_obj_X _ _ _ _ hs)
      (fun t ht => HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_tateTwist_mul_degreeZero_hom q i j k hk τ
  have hsurj := GlobalTheory.T.tateTwist_mul_degreeZero_locally_surjective q i j k hk τ hτ φ hφ
  have hinj := GlobalTheory.T.tateTwist_mul_degreeZero_locally_injective q i j k hk (GlobalTheory.T.tateTwistGenerator_tmul_order_locally q i j) τ hτ φ hφ
  have hM := GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections (ZMod q) φ
  haveI : Mono φ := hM.2.1.2 hinj
  haveI : Epi φ := hM.2.2.1.2 hsurj
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  let u : K ⟶ sgl (tw q k) := HomologicalComplex.mkHomToSingle (inv φ) (fun a ha => (hzK a (by simp at ha; omega)).eq_of_src _ _)
  have hu0 : u.f 0 = inv φ ≫ sglι (tw q k) := HomologicalComplex.mkHomToSingle_f _ _
  haveI : ∀ w, IsIso (u.f w) := by
    intro w
    by_cases hw : w = 0
    · subst hw; rw [hu0]; unfold sglι; exact IsIso.comp_isIso' inferInstance (Iso.isIso_inv _)
    · exact ⟨⟨0, (hzK w hw).eq_of_src _ _, (HomologicalComplex.isZero_single_obj_X _ _ _ _ hw).eq_of_src _ _⟩⟩
  haveI : IsIso u := HomologicalComplex.Hom.isIso_of_components u
  obtain ⟨ν, hν⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).2.2 u
  refine ⟨ν, GlobalTheory.T.isTensor_of_compat_isIso_target (ZMod q) τ ν u inferInstance hν hτ, fun U ζ => ?_⟩
  have h := hν U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))
  simp only [HomologicalComplex.id_f, secMap_id] at h
  rw [← h, ← hφ, hu0, secMap_comp, ← secMap_comp φ (inv φ), IsIso.hom_inv_id, secMap_id]

end GlobalTheory.EtC.TwMul
