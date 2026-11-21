import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLetters
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

section
open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

section Th

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def alG (s A : ℝ) (x : T → I → J → ℂ) : ℂ := (-1 : ℂ) ^ (round (s * (HfG A x x).re))

def ThSpG (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Set ((T → I → J → ℂ) → ℂ) :=
  {G | Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, alG s A x * UG A x G z = G z}

noncomputable def normSqG (A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) (G : (T → I → J → ℂ) → ℂ) : ℝ :=
  let Fd : Set (T → I → J → ℂ) :=
    Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain La' Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re)

noncomputable def IopG (s A : ℝ) (La₁ La₂ : AddSubgroup (T → I → J → ℂ)) (G : (T → I → J → ℂ) → ℂ) :
    (T → I → J → ℂ) → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      alG s A ((Quotient.out q : La₂) : T → I → J → ℂ) * UG A ((Quotient.out q : La₂) : T → I → J → ℂ) G z

def GoodLat (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Prop :=
  (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (T → I → J → ℂ)), La' = AddSubgroup.closure (Set.range b)) ∧
  (∀ x ∈ La', ∀ y ∈ La', ∃ n : ℤ, (HfG A x y).im = n) ∧
  (∀ v : T → I → J → ℂ, (∀ x ∈ La', ∃ n : ℤ, (HfG A v x).im = n) → v ∈ La') ∧
  ∀ x ∈ La', ∀ y ∈ La', ∀ n : ℤ, (HfG A x y).im = n → alG s A (x + y) = alG s A x * alG s A y * (-1 : ℂ) ^ n

end Th

def ThetaLineG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La' : AddSubgroup (T → I → J → ℂ), GoodLat s A La' →
      ∃ G ∈ ThSpG s A La', G ≠ 0 ∧ ∀ F ∈ ThSpG s A La', ∃ c : ℂ, F = fun z => c * G z

def IopUnitaryG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La₁ La₂ : AddSubgroup (T → I → J → ℂ), GoodLat s A La₁ → GoodLat s A La₂ →
      (La₁.addSubgroupOf La₂).index ≠ 0 → (La₂.addSubgroupOf La₁).index ≠ 0 →
      ∀ th ∈ ThSpG s A La₁,
        IopG s A La₁ La₂ th ∈ ThSpG s A La₂ ∧
        normSqG A La₂ (IopG s A La₁ La₂ th) = normSqG A La₁ th ∧
        IopG s A La₂ La₁ (IopG s A La₁ La₂ th) = th

def GoodLa (D : D7) : Prop :=
  ∀ (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    0 < area (lamOf D cc δ) ∧
    ∀ (N N' : ℕ) (L₁ L₂ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E))
      (L₁' L₂' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N' → D.host.E)), admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
      GoodLat (Real.sqrt D.host.d / 2) (area (lamOf D cc δ)) (La D (tor0 D cc δ) L₁ L₁') ∧
      ((La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) L₂ L₂')).index ≠ 0

end Formalism.MainNotions.Ext
end

section
open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

section Lat

variable {E : Type} [Field E] [NumberField E]

def gYY (MM : Submodule (𝓞 E) E) {N N' : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) :
    Submodule (𝓞 E) (Matrix (Fin N') (Fin N) E) :=
  Submodule.span (𝓞 E)
    {B | ∃ a ∈ MM, ∃ A ∈ Submodule.span (𝓞 E) {A : Matrix (Fin N') (Fin N) E | ∀ x ∈ L, A.mulVec x ∈ L'}, B = a • A}

def gLa {S : Type} (emb : S → E →+* ℂ) (abelian₂ : AddSubgroup ℂ) (MM : Submodule (𝓞 E) E) {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) : AddSubgroup (S → Fin N' → Fin N → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ abelian₂, ∃ A ∈ gYY MM L L', z = w • (fun s i j => emb s (A i j))}

end Lat

def GoodLatCM : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) →
  ∀ (K : IntermediateField ℚ E) (d : ℕ), Module.finrank ℚ K = 2 → discr K = -(d : ℤ) → d % 4 = 3 →
  ∀ (φ₀ : E →+* ℂ) (S : Type) [Fintype S] (emb : S → E →+* ℂ), Function.Injective emb →
    (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) → Fintype.card S = Module.finrank K E →
  ∀ MM : Submodule (𝓞 E) E, MM.FG → MM ≠ ⊥ →
    (∀ x : E, x ∈ MM ↔ ∀ y ∈ MM, Algebra.trace K E (x * star y) ∈ (algebraMap (𝓞 K) K).range) →
  ∀ (cc : Ideal (𝓞 K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 →
  ∀ (N N' : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin N → E)) (L₁' L₂' : Submodule (𝓞 E) (Fin N' → E)),
    IsSDLat E N L₁ → IsSDLat E N' L₁' → IsSDLat E N L₂ → IsSDLat E N' L₂' →
    GoodLat (Real.sqrt d / 2) (area (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}))
      (gLa emb (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}) MM L₁ L₁') ∧
    ((gLa emb (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}) MM L₁ L₁').addSubgroupOf
      (gLa emb (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}) MM L₂ L₂')).index ≠ 0

end Formalism.MainNotions.Ext

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

theorem discr_K {R : Ranks} (H : Host R) : discr H.K = -(H.d : ℤ) := by
  obtain ⟨-, hdp, -, hd16, -⟩ := H.hyp
  have hm : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ H.sqd
  have hx : (⟨H.sqd, hm⟩ : H.K) ^ 2 = ((-(H.d : ℤ) : ℤ) : H.K) := by
    apply Subtype.ext
    push_cast
    exact H.sqd_sq
  refine Formalism.HF.P.quadDiscr_ne_one H.K (-(H.d : ℤ)) _ hx ?_ ?_ ?_ ?_
  · have key : @IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {⟨H.sqd, hm⟩} = ⊤ := by
      apply IntermediateField.map_injective (IntermediateField.val H.K)
      rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
        Set.image_singleton]
      first
      | rfl
      | (simp only [IntermediateField.val_mk]; rfl)
      | simp [Formalism.HC.HostRaw.K]
    convert key
    all_goals first
      | exact Subsingleton.elim _ _
      | (apply Algebra.algebra_ext; intro r; simp [Algebra.algebraMap_eq_smul_one])
  · exact Int.squarefree_natAbs.mp (by simpa using hdp.prime.squarefree)
  · omega
  · omega

end Formalism.MainNotions.Ext
end
