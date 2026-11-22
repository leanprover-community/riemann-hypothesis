module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EventuallySelfDualLatticeIndicatorIsVacuum

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology

namespace GlobalTheory.VacIndic

variable {F : Type} [Field F] [NumberField F]

theorem evFin_algebraMap (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    evFin F v (algebraMap F (AF F) x) = algebraMap F (Fv F v) x := (evFin F v).commutes x

theorem eq_of_at {v : HeightOneSpectrum (𝓞 F)} {a : AF F} (ha : At (evFin F v) a) :
    a = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v a)) := by
  set e : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1) with he
  have hev : evFin F v e = 1 := by
    show evalV F v (singleFin v 1) = 1
    exact evalV_singleFin_self v 1
  have h1 : (1 - e) • a = 0 := ha _ (by rw [map_sub, map_one, hev, sub_self])
  have h2 : a = e * a := by
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1; exact h1
  rw [h2]
  refine Prod.ext ?_ ?_
  · show (0 : Ainf F) * a.1 = 0; rw [zero_mul]
  · apply af_ext
    intro u
    show evalV F u (singleFin v 1 * a.2) = evalV F u (singleFin v (evFin F v (e * a)))
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, one_mul, map_mul, hev, one_mul]; rfl
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]

theorem psi_of_at (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)} {a : AF F} (ha : At (evFin F v) a) :
    ψ a = psiLoc ψ v (evFin F v a) := by
  conv_lhs => rw [eq_of_at ha]
  rfl

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F : Type} [Field F] [NumberField F]

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F : Type} [Field F] [NumberField F]

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F : Type} [Field F] [NumberField F]

section AtLemmas

variable {v : HeightOneSpectrum (𝓞 F)}

theorem at_mul_left {a b : AF F} (hb : At (evFin F v) b) : At (evFin F v) (a * b) := fun u hu => by
  rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u b, hb u hu, mul_zero]

theorem at_add {a b : AF F} (ha : At (evFin F v) a) (hb : At (evFin F v) b) : At (evFin F v) (a + b) :=
  fun u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]

theorem at_sum {ι : Type} (s : Finset ι) (f : ι → AF F) (h : ∀ i, At (evFin F v) (f i)) :
    At (evFin F v) (∑ i ∈ s, f i) := fun u hu => by
  rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => h i u hu

theorem at_pi {κ : Type} {z : κ → AF F} (h : ∀ k, At (evFin F v) (z k)) : At (evFin F v) z :=
  fun u hu => funext fun k => by simpa using h k u hu

end AtLemmas

theorem invOf_two_eq : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_left_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  norm_num

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := rfl

theorem smul_inclR_eq (c : AF F) (e : E) : c • inclR (F := F) (AF F) e = c ⊗ₜ[F] e := by
  show c • ((1 : AF F) ⊗ₜ[F] e) = c ⊗ₜ[F] e
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem trace_inclR [FiniteDimensional F E] (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

variable {n d : ℕ}

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

section SympAdd

variable {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') (ξ : E')
  {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α E') (JB : Matrix β β E')

theorem symp_zero_left (y : Matrix α β E') : symp c ξ JA JB 0 y = 0 := by
  simp only [symp, hTens, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, map_zero]

end SympAdd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {n d : ℕ}

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.VacIndic

namespace GlobalTheory.VacIndic

theorem eventually_isVac_indicator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) :=
  Tw.VacIndic.eventually_isVac_indicator

end GlobalTheory.VacIndic
