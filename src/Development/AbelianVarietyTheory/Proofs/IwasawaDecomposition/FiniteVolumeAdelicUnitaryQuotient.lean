module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightedSupDriftOnOrthonormalFrames
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDataLattice
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverOfDriftFunction
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeGramEqSgn, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeRealPoints, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralConj, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPoints, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeGramEqSgn =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeGramEqSgn", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open NumberField

namespace GlobalTheory.HermSignature

theorem exists_le_gram_eq_sgn : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → ∀ τ : E →+* ℂ, ∃ p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧ ReciprocityTheory.ChartRestriction.G.FD.gram τ G P = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  intro E _ _ _ r G hG hd τ
  obtain ⟨p, Q, hQ, h⟩ := GlobalTheory.Published.LandherrSt.exists_gram_eq_sgn hG hd τ
  refine ⟨min p r, min_le_right _ _, Q, hQ, ?_⟩
  rw [h]
  congr 1
  funext a
  have ha := a.2
  simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, lt_min_iff, ha, and_true]

end GlobalTheory.HermSignature
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeGramEqSgn =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeRealPoints =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeRealPoints", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.CovolTransport

section General

theorem isometry_iff {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (J g : Matrix (Fin M) (Fin M) A) :
    (∀ u w : Fin M → A, ∑ a, ∑ b, (g *ᵥ u) a * J b a * s ((g *ᵥ w) b) = ∑ a, ∑ b, u a * J b a * s (w b)) ↔
      Formalism.UG.cT s g * J * g = J := by
  have h1 : ∀ (K : Matrix (Fin M) (Fin M) A) (u w : Fin M → A),
      ∑ a, ∑ b, u a * K b a * s (w b) = (s ∘ w) ⬝ᵥ (K *ᵥ u) := by
    intro K u w
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : ∀ u w : Fin M → A, (s ∘ (g *ᵥ w)) ⬝ᵥ (J *ᵥ (g *ᵥ u)) =
      (s ∘ w) ⬝ᵥ ((Formalism.UG.cT s g * J * g) *ᵥ u) := by
    intro u w
    have e : s ∘ (g *ᵥ w) = g.map s *ᵥ (s ∘ w) := by
      funext a; exact RingHom.map_mulVec s g w a
    rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    rfl
  simp only [h1, h2]
  constructor
  · intro h
    ext a b
    have := h (Pi.single b 1) (Pi.single a 1)
    have e : s ∘ (Pi.single a 1 : Fin M → A) = Pi.single a 1 := by
      funext k
      by_cases hk : k = a <;> simp [hk]
    rw [e] at this
    simpa using this
  · intro h u w
    rw [h]

variable {S : Type} [CommRing S] {I : Type} {M : ℕ} {e : S ≃+* (I → ℂ)} {θ : I → (S →+* ℂ)}

theorem ext_map (he : ∀ x i, e x i = θ i x) {X Y : Matrix (Fin M) (Fin M) S}
    (h : ∀ i, X.map (θ i) = Y.map (θ i)) : X = Y := by
  ext a b
  apply e.injective
  funext i
  rw [he, he]
  exact congrFun (congrFun (h i) a) b

theorem cT_map {s : S →+* S} {t : S →+* ℂ} (hs : ∀ x, t (s x) = star (t x))
    (X : Matrix (Fin M) (Fin M) S) :
    (Formalism.UG.cT s X).map t = Formalism.UG.cT (starRingEnd ℂ) (X.map t) := by
  ext a b
  simp [Formalism.UG.cT, hs]

theorem exists_equiv [TopologicalSpace S] (he : ∀ x i, e x i = θ i x) (hc : Continuous e)
    (hc' : Continuous e.symm) (s : S →+* S) (hs : ∀ x i, θ i (s x) = star (θ i x))
    (J : Matrix (Fin M) (Fin M) S) (H : Subgroup (I → GL (Fin M) ℂ))
    (hH : ∀ g, g ∈ H ↔ ∀ i, g i ∈ Formalism.UG.UJ (starRingEnd ℂ) (J.map (θ i))) :
    ∃ f : Formalism.UG.UJ s J ≃ₜ* H, ∀ h i, (((f h : I → GL (Fin M) ℂ) i : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) =
      ((h.1 : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).map (θ i) := by
  have hone : ∀ i, (1 : Matrix (Fin M) (Fin M) S).map (θ i) = 1 := fun i =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hθ : ∀ i, Continuous (θ i) := fun i => by
    have : (θ i : S → ℂ) = fun x => e x i := funext fun x => (he x i).symm
    rw [this]
    exact (continuous_apply i).comp hc
  let fw : Formalism.UG.UJ s J → H := fun h => ⟨fun i => Formalism.UG.bc (θ i) h.1, (hH _).2 fun i => by
    have hh : Formalism.UG.cT s h.1.1 * J * h.1.1 = J := h.2
    have h2 := congrArg (fun X => Matrix.map X (θ i)) hh
    simp only [Matrix.map_mul, cT_map (fun x => hs x i)] at h2
    exact h2⟩
  have hfw : ∀ h i, ((fw h).1 i).1 = h.1.1.map (θ i) := fun _ _ => rfl
  let L : H → Matrix (Fin M) (Fin M) S :=
    fun g => Matrix.of fun a b => e.symm fun i => (g.1 i).1 a b
  have hL : ∀ g i, (L g).map (θ i) = (g.1 i).1 := fun g i => by
    ext a b
    simp [L, ← he]
  have hLmul : ∀ g g', L g * L g' = L (g * g') := by
    intro g g'
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, hL, hL, hL]
    rfl
  have hL1 : L 1 = 1 := by
    refine ext_map he fun i => ?_
    rw [hL, hone]
    rfl
  have hLu : ∀ g, Formalism.UG.cT s (L g) * J * L g = J := by
    intro g
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (fun x => hs x i), hL]
    exact (hH _).1 g.2 i
  have hLc : Continuous L := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine hc'.comp (continuous_pi fun i => ?_)
    have : Continuous fun g : H => (g.1 i).1 :=
      Units.continuous_val.comp ((continuous_apply i).comp continuous_subtype_val)
    exact this.matrix_elem a b
  let bw : H → Formalism.UG.UJ s J := fun g =>
    ⟨⟨L g, L g⁻¹, by rw [hLmul, mul_inv_cancel, hL1], by rw [hLmul, inv_mul_cancel, hL1]⟩, hLu g⟩
  refine ⟨
    { toFun := fw
      invFun := bw
      left_inv := fun h => ?_
      right_inv := fun g => ?_
      map_mul' := fun h h' => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun h i => rfl⟩
  · exact Subtype.ext (Units.ext (ext_map he fun i => hL (fw h) i))
  · exact Subtype.ext (funext fun i => Units.ext (hL g i))
  · exact Subtype.ext (funext fun i => map_mul (Formalism.UG.bc (θ i)) h.1 h'.1)
  · refine Continuous.subtype_mk (continuous_pi fun i => Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (hθ i)
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (hθ i)
  · exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨hLc, hLc.comp continuous_inv⟩) _

end General

theorem isCMFam_val {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    IsCMFam (fun τ : Ψ => τ.1) := by
  constructor
  · intro i j hij
    rcases InfinitePlace.mk_eq_iff.1 hij with h | h
    · exact Subtype.ext h
    · exact absurd (h ▸ j.2) ((hΨ _).1 i.2)
  · intro w
    by_cases h : w.embedding ∈ Ψ
    · exact ⟨⟨_, h⟩, w.mk_embedding⟩
    · have h' : ComplexEmbedding.conjugate w.embedding ∈ Ψ := by
        by_contra hn
        exact h ((hΨ _).2 hn)
      exact ⟨⟨_, h'⟩, (InfinitePlace.mk_conjugate_eq _).trans w.mk_embedding⟩

theorem finite_covolume_real_points : (∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ Ψ : Finset (E →+* ℂ), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ NumberField.ComplexEmbedding.conjugate τ ∉ Ψ) ∧ ∀ (H : Subgroup (Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ ∀ τ : Ψ, ∀ u w : Fin r → ℂ, ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) u) (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) w) = ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G u w) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : MeasureTheory.Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab G Λ γ ∧ ∃ w ∈ Ω, ∀ τ : Ψ, (((g : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∀ ν : Measure (HA (Ainf F) σ J), ν.IsHaarMeasure → ∃ Ω : Set (HA (Ainf F) σ J), MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : HA (Ainf F) σ J, ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, (∀ x, x ∈ L ↔ (γ : Matrix (Fin M) (Fin M) E).mulVec x ∈ L) ∧ ∃ w ∈ Ω, HA.mat (Ainf F) σ J g = Formalism.UG.bc (inclR (F := F) (Ainf F)) γ * HA.mat (Ainf F) σ J w := by
  intro hyp F E _ _ _ _ _ σ hcm M J hJ L hL hsp ν hν
  haveI := hcm.1
  haveI := hcm.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = σ x := fun x => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply φ.injective
    rw [ReciprocityTheory.ChartRestriction.G.FD.emb_cc, hcm.2.2.2]
    rfl
  obtain ⟨Ψ, hΨ, hcov⟩ := hyp E M Jᵀ L (fun a b => by rw [hcc]; exact hJ.1 a b)
    (by rw [Matrix.det_transpose]; exact hJ.2) hL hsp
  choose θ hθ using fun τ : Ψ => (GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E σ hcm τ.1).exists
  obtain ⟨e, he, hc, hc', hs⟩ :=
    GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ Ψ _ θ hcm (isCMFam_val Ψ hΨ) hθ
  have hincl : ∀ (X : Matrix (Fin M) (Fin M) E) (τ : Ψ),
      (X.map (inclR (F := F) (Ainf F))).map (θ τ) = X.map τ.1 := fun X τ => by
    ext a b
    exact (hθ τ).1 (X a b)
  let H : Subgroup (Ψ → GL (Fin M) ℂ) :=
    Subgroup.pi Set.univ fun τ => Formalism.UG.UJ (starRingEnd ℂ) (J.map τ.1)
  obtain ⟨f, hf⟩ : ∃ f : HA (Ainf F) σ J ≃ₜ* H, ∀ h i,
      (((f h : Ψ → GL (Fin M) ℂ) i : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) =
        (HA.mat (Ainf F) σ J h : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) :=
    exists_equiv he hc hc' (sigR (Ainf F) σ) (fun x i => by rw [← he, ← he, hs]) (JR (Ainf F) J) H
      fun g => by
        simp only [H, Subgroup.mem_pi, Set.mem_univ, forall_const, JR, hincl]
  borelize ↥H
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (Ainf F) σ J) :=
    f.toHomeomorph.isInducing.topologicalGroup f
  haveI : (ν.map f).IsHaarMeasure := f.isHaarMeasure_map ν
  obtain ⟨Ω, hΩm, hΩf, hΩ⟩ := hcov H (fun g => by
    simp only [H, Subgroup.mem_pi, Set.mem_univ, forall_const]
    exact forall_congr' fun τ => (isometry_iff (starRingEnd ℂ) (J.map τ.1) (g τ).1).symm) (ν.map f)
  have hfm : Measurable f := f.continuous.measurable
  refine ⟨f ⁻¹' Ω, hfm hΩm, by rwa [Measure.map_apply hfm hΩm] at hΩf, fun g => ?_⟩
  obtain ⟨γ, hγ, w, hw, hgw⟩ := hΩ (f g)
  refine ⟨γ, (isometry_iff (σ : E →+* E) J γ.1).1 fun u v => ?_, hγ.2, f.symm w, by simpa using hw, ?_⟩
  · have := hγ.1 u v
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, hcc, Matrix.transpose_apply] at this
    exact this
  · refine Units.ext (ext_map he fun τ => ?_)
    rw [Units.val_mul, Matrix.map_mul, ← hf, ← hf, f.apply_symm_apply, hgw, ← hincl]
    rfl

end GlobalTheory.Mem.CovolTransport
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeRealPoints =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralConj =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralConj", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField

namespace GlobalTheory.HermDen

open ReciprocityTheory.ChartRestriction.G.FD

theorem isIntegral_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {x : E}
    (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom

theorem exists_den (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ Λ, ∀ y ∈ Λ,
      IsIntegral ℤ ((den : E) * ReciprocityTheory.ChartRestriction.G.FD.herm G x y) := by
  classical
  obtain ⟨k, hk, hi⟩ := GlobalTheory.LatFin.exists_common_den Λ hΛ
  obtain ⟨l, hl, hG⟩ := GlobalTheory.LatFin.exists_common_den
    (Submodule.span (𝓞 E) (Set.range fun a : Fin r => (G a : Fin r → E)))
    (Submodule.fg_span (Set.finite_range _))
  have hG' : ∀ a b, IsIntegral ℤ ((l : E) * G a b) := fun a b =>
    hG _ (Submodule.subset_span ⟨a, rfl⟩) b
  refine ⟨((k * k * l : ℤ) : 𝓞 E), Int.cast_ne_zero.2 (mul_ne_zero (mul_ne_zero hk hk) hl),
    fun x hx y hy => ?_⟩
  have e : ((((k * k * l : ℤ) : 𝓞 E)) : E) * herm G x y
      = ∑ a, ∑ b, ((k : E) * x a) * ((l : E) * G a b) * cc ((k : E) * y b) := by
    have h1 : ((((k * k * l : ℤ) : 𝓞 E)) : E) = (k : E) * k * l := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_intCast]
      push_cast
      ring
    rw [h1, herm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h2 : cc ((k : E) * y b) = k * cc (y b) := by simp [cc]
    rw [h2]
    ring
  rw [e]
  exact IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ =>
    ((hi x hx a).mul (hG' a b)).mul (isIntegral_conj (hi y hy b))

end GlobalTheory.HermDen
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralConj =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPoints =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPoints", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightedSupDriftOnOrthonormalFrames\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundOrthonormalFrame\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDataLattice\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeGramEqSgn\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeRealPoints\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralConj\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverOfDriftFunction\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory.MixedSignature

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem compact_mod_stabiliser_of_minGe :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) {den : 𝓞 E} (_ : den ≠ 0) (_ : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((den : E) * herm G x y)) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, Orth X G p x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, MinGe X ε (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by
  intro r X G p hG den hden hint H hH x0 hx0 ε hε
  obtain ⟨-, -, hfr⟩ := unitary_group_frames r X p H hH
  obtain ⟨horth, ι, hιc, -, hιg⟩ := hfr x0 hx0
  obtain ⟨R, hR⟩ := exists_bound_orthonormal_frame X G p hG hden hint ε hε
  obtain ⟨Γ, hΓ⟩ := exists_stabiliser_image_subgroup r X H hH
  refine ⟨ι '' {x : Frame X.Ψ r | Orth X G p x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R},
    (isCompact_orth_bounded r X G p R).image_of_continuousOn
      (hιc.mono fun x hx => hx.1), fun g hg => ?_⟩
  obtain ⟨γ, hγ, hb⟩ := hR _ (horth g) hg
  obtain ⟨u, hu⟩ := exists_unitary_elem_of_isUStab r X H hH γ hγ
  have huΓ : u ∈ Γ := (hΓ u).2 ⟨γ, hγ, hu⟩
  refine ⟨u⁻¹, (hΓ _).1 (Γ.inv_mem huΓ), u * g, ⟨_, ⟨horth (u * g), ?_⟩, hιg (u * g)⟩,
    (inv_mul_cancel_left u g).symm⟩
  have key : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) x0 = lact γ (X.lmulC (fun τ =>
        (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
    funext τ
    change (((u : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) * mat x0 τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x0 τ)
    rw [hu, Matrix.mul_assoc]
  rw [key]
  exact hb

theorem exists_finite_measure_cover : (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) {den : 𝓞 E} (_ : den ≠ 0) (_ : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((den : E) * herm G x y)) (x0 : Frame X.Ψ r) (_ : Orth X G p x0) (_ : ∀ τ, p τ ≤ r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  intro r X G p hG den hden hint x0 hx0 hple H hH _ _ ν _
  obtain ⟨Γ, hΓ⟩ := exists_stabiliser_image_subgroup r X H hH
  suffices hS : ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w by
    obtain ⟨Ω, h1, h2, h3⟩ := hS
    refine ⟨Ω, h1, h2, fun g => ?_⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := h3 g
    obtain ⟨γ, hγ, hγu⟩ := (hΓ u).1 hu
    refine ⟨γ, hγ, w, hw, fun τ => ?_⟩
    rw [← hγu τ]
    simp
  by_cases hp : ∀ τ, p τ = 0 ∨ p τ = r
  · have : CompactSpace H := compactSpace_unitary_of_definite r X H hH hp x0 hx0
    exact ⟨Set.univ, MeasurableSet.univ, isCompact_univ.measure_lt_top,
      fun g => ⟨1, Γ.one_mem, g, Set.mem_univ _, (one_mul g).symm⟩⟩
  · obtain ⟨τ0, hp⟩ := not_forall.1 hp
    have hp0 : 0 < p τ0 := Nat.pos_of_ne_zero fun h => hp (Or.inl h)
    have hpr : p τ0 < r := lt_of_le_of_ne (hple τ0) fun h => hp (Or.inr h)
    obtain ⟨hlc, hsc, -⟩ := unitary_group_frames r X p H hH
    obtain ⟨σ, _, _, h, f, c, b, hk, hf, hf0, hinv, hc0, hc1, hb, hdrift, hsub⟩ :=
      exists_drift_function r X G p hG τ0 H hH hp0 hpr x0 hx0
    obtain ⟨U, hU, hU1⟩ := gamDisc r X H hH
    refine GlobalTheory.exists_finite_measure_cover_of_drift_function H ν Γ σ h f c b
      ⟨U, hU, fun γ hγ => hU1 γ ((hΓ γ).1 hγ)⟩ hk hf hf0
      (fun γ hγ => hinv γ ((hΓ γ).1 hγ)) hc0 hc1 hb hdrift fun M => ?_
    obtain ⟨ε, hε, hM⟩ := hsub M
    obtain ⟨K, hK, hKc⟩ := compact_mod_stabiliser_of_minGe r X G p hG hden hint H hH x0 hx0 ε hε
    refine ⟨K, hK, fun g hg => ?_⟩
    obtain ⟨u, hu, k, hk, e⟩ := hKc g (hM g hg)
    exact ⟨u, (hΓ u).2 hu, k, hk, e⟩

end


open NumberField in
theorem exists_cmType_finite_measure_cover : (∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ Ψ : Finset (E →+* ℂ), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ NumberField.ComplexEmbedding.conjugate τ ∉ Ψ) ∧ ∀ (H : Subgroup (Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ ∀ τ : Ψ, ∀ u w : Fin r → ℂ, ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) u) (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) w) = ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G u w) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : MeasureTheory.Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab G Λ γ ∧ ∃ w ∈ Ω, ∀ τ : Ψ, (((g : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  intro E _ _ _ r G Λ hh hG hfg hsp
  obtain ⟨X, rfl⟩ := GlobalTheory.Member.LatData.exists_data_lattice E r Λ hfg hsp
  obtain ⟨den, hden, hint⟩ := GlobalTheory.HermDen.exists_den E r G X.Λ hfg
  choose p hp P _ hP using fun τ : X.Ψ => GlobalTheory.HermSignature.exists_le_gram_eq_sgn E r G hh hG τ.1
  exact ⟨X.Ψ, X.cmType, exists_finite_measure_cover r X G p hG hden hint P hP hp⟩

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem finite_covolume_real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∀ ν : Measure (HA (Ainf F) σ J), ν.IsHaarMeasure → ∃ Ω : Set (HA (Ainf F) σ J), MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : HA (Ainf F) σ J, ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, (∀ x, x ∈ L ↔ (γ : Matrix (Fin M) (Fin M) E).mulVec x ∈ L) ∧ ∃ w ∈ Ω, HA.mat (Ainf F) σ J g = Formalism.UG.bc (inclR (F := F) (Ainf F)) γ * HA.mat (Ainf F) σ J w :=
  GlobalTheory.Mem.CovolTransport.finite_covolume_real_points exists_cmType_finite_measure_cover

end GlobalTheory.MixedSignature
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPoints =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff\npublic import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1\npublic import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPoints\npublic import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct Pointwise

namespace GlobalTheory.Mem.VolFin

theorem measure_lt_top_of_cover {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B]
    (e : G ≃ₜ* A × B) (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure]
    (S : Finset B) (K : Set B) (hK : IsCompact K) (Ω : B → Set A)
    (hΩ : ∀ s, (Measure.haar : Measure A) (Ω s) < ⊤)
    (hcov : ∀ g : G, ∃ γ : Γ, ∃ s ∈ S, (e (γ • g)).1 ∈ Ω s ∧ (e (γ • g)).2 ∈ s • K)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have h1 : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  have h2 := Measure.isMulLeftInvariant_eq_smul (μ.map e)
    ((Measure.haar : Measure A).prod (Measure.haar : Measure B))
  have hle : μ 𝓕 ≤ μ (⋃ s ∈ S, e ⁻¹' (Ω s ×ˢ (s • K))) := by
    refine GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers h𝓕 (.of_forall fun g => ?_)
    obtain ⟨γ, s, hs, h⟩ := hcov g
    exact ⟨γ, Set.mem_biUnion hs h⟩
  refine hle.trans_lt ((measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.2 fun s _ => ?_))
  refine (Measure.le_map_apply (map_continuous e).measurable.aemeasurable _).trans_lt ?_
  rw [h2, Measure.smul_apply, Measure.prod_prod]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top (hΩ s) (hK.smul s).measure_lt_top)

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  simp [sigR, inclR]

noncomputable def ratPt (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Formalism.UG.UJ (σ : E →+* E) J →* HA R σ J where
  toFun γ := (⟨Formalism.UG.bc (inclR (F := F) R) γ.1, by
    have := congrArg (fun N => N.map (inclR (F := F) R)) (show Formalism.UG.cT _ _ * _ * _ = _ from γ.2)
    simp only [Matrix.map_mul] at this
    change Formalism.UG.cT _ _ * _ * _ = _
    refine Eq.trans ?_ this
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ rfl) rfl
    ext i j
    exact sigR_inclR R σ _⟩ : HR R σ J)
  map_one' := Subtype.ext (map_one (Formalism.UG.bc (inclR (F := F) R)))
  map_mul' a b := Subtype.ext (map_mul (Formalism.UG.bc (inclR (F := F) R)) _ _)

theorem topGroup_HA [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem countable_HFinIn [Countable E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Countable (HFinIn R σ J) := by
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  refine Function.Surjective.countable
    (f := fun γ : Formalism.UG.UJ (σ : E →+* E) J => (⟨ratPt R σ J γ, γ.1, γ.2, rfl⟩ : HFinIn R σ J)) ?_
  rintro ⟨g, γ, hγ, h⟩
  exact ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext h)⟩

variable [NumberField F]

theorem mulVec_fv {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (m.map (inclR (F := F) (Af F))).mulVec (GlobalTheory.AdLat.fv F x) = GlobalTheory.AdLat.fv F (m.mulVec x) := by
  ext i
  exact (RingHom.map_mulVec (inclR (F := F) (Af F)) m x i).symm

theorem mulVec_mem_hat_of_rat {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (h : ∀ x ∈ Λ, m.mulVec x ∈ Λ) {z : Fin M → Af F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))) :
    (m.map (inclR (F := F) (Af F))).mulVec z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
  refine GlobalTheory.AdLat.Translate.mulVec_mem_hat (fun x hx => ?_) hz
  rw [SetLike.mem_coe, GlobalTheory.AdLat.Translate.mem_pre, mulVec_fv]
  exact GlobalTheory.AdLat.Translate.fv_mem_hat (h x hx)

theorem stabHat_conj {M : ℕ} (δ : GL (Fin M) E) (L Λ : Submodule (𝓞 E) (Fin M → E))
    (s : GL (Fin M) (Af F ⊗[F] E))
    (hΛ : (GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) : Set (Fin M → Af F ⊗[F] E)) =
      (s : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin M → E))))
    (h : ∀ x, x ∈ Λ ↔ (δ : Matrix (Fin M) (Fin M) E).mulVec x ∈ Λ) :
    StabHat F (L : Set (Fin M → E))
      ((s⁻¹ * Formalism.UG.bc (inclR (F := F) (Af F)) δ * s : GL (Fin M) (Af F ⊗[F] E)) :
        Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) := by
  have him : ∀ y, y ∈ latHat F E (L : Set (Fin M → E)) ↔
      (s : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
    intro y
    rw [← SetLike.mem_coe (p := GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))), hΛ]
    constructor
    · exact fun hy => ⟨y, hy, rfl⟩
    · rintro ⟨u, hu, huy⟩
      have := congrArg ((s⁻¹ : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec huy
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at this
      exact this ▸ hu
  intro y
  rw [him, him, Matrix.mulVec_mulVec y, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
    Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨mulVec_mem_hat_of_rat _ Λ fun x hx => (h x).1 hx, fun hz => ?_⟩
  have := mulVec_mem_hat_of_rat ((δ⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Λ (fun x hx => by
    rw [h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hx) hz
  change ((Formalism.UG.bc (inclR (F := F) (Af F)) δ⁻¹ : GL (Fin M) (Af F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec _ ∈ _ at this
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at this

end Rat

theorem finVol : FiniteVolume₂ := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ hμ 𝓕 h𝓕
  classical
  haveI := topGroup_HA (AF F) σ J
  haveI := topGroup_HA (Ainf F) σ J
  haveI := topGroup_HA (Af F) σ J
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Ainf F) σ M J
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Af F) σ M J
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI : Countable Γ := countable_HFinIn (AF F) σ J
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E σ M J
  have herat : ∀ γ, e (ratPt (AF F) σ J γ) = (ratPt (Ainf F) σ J γ, ratPt (Af F) σ J γ) := by
    intro γ
    refine Prod.ext (Subtype.ext (Units.ext ((he _).2.trans ?_))) (Subtype.ext (Units.ext ((he _).1.trans ?_)))
    · ext i j
      change Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (Ainf F) _
      simp [inclR]
    · ext i j
      change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (Af F) _
      simp [inclR]
  let b := Pi.basisFun E (Fin M)
  let L : Submodule (𝓞 E) (Fin M → E) := Submodule.span (𝓞 E) (Set.range b)
  have hL : L.FG := Submodule.fg_span (Set.finite_range b)
  have hLs : Submodule.span E (L : Set (Fin M → E)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨K, hK, hKo, hKc⟩ := _root_.GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E σ M J L hL hLs
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.Mem.ClassFinite.exists_finset_classes F E σ hCM M J hJ K hKo
  choose Λ _ hΛ1 hΛ2 hΛ3 using fun s : HA (Af F) σ J =>
    GlobalTheory.AdLat.exists_lattice_latOf F E M L (HA.mat (Af F) σ J s) hL hLs
  choose Ω _ hΩ1 hΩ2 using fun s : HA (Af F) σ J =>
    _root_.GlobalTheory.MixedSignature.finite_covolume_real_points F E σ hCM M J hJ (Λ s) (hΛ1 s) (hΛ2 s) Measure.haar inferInstance
  refine measure_lt_top_of_cover e Γ μ S K hKc Ω hΩ1 (fun g => ?_) 𝓕 h𝓕
  obtain ⟨⟨γ', γ, hγ, hγγ⟩, s, hs, k, hk, hg⟩ := hS (e g).2
  have hg2 : (e g).2 = ratPt (Af F) σ J ⟨γ, hγ⟩ * (s * k) := by
    rw [hg]
    exact congrArg (· * (s * k)) (Subtype.ext hγγ.symm : (γ' : HA (Af F) σ J) = ratPt (Af F) σ J ⟨γ, hγ⟩)
  obtain ⟨δ, hδ, hδΛ, w, hw, hwe⟩ := hΩ2 s ((ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1)
  have hw1 : (ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1 = ratPt (Ainf F) σ J ⟨δ, hδ⟩ * w := Subtype.ext hwe
  have hkδ : s⁻¹ * ratPt (Af F) σ J ⟨δ, hδ⟩ * s ∈ K :=
    (hK _).2 (stabHat_conj δ L (Λ s) (HA.mat (Af F) σ J s) (hΛ3 s) hδΛ)
  let η : Formalism.UG.UJ (σ : E →+* E) J := (⟨δ, hδ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹ * (⟨γ, hγ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹
  refine ⟨⟨ratPt (AF F) σ J η, η.1, η.2, rfl⟩, s, hs, ?_, ?_⟩
  · change (e (ratPt (AF F) σ J η * g)).1 ∈ _
    rw [map_mul, herat, Prod.fst_mul, map_mul, map_inv, map_inv, mul_assoc, hw1, inv_mul_cancel_left]
    exact hw
  · change (e (ratPt (AF F) σ J η * g)).2 ∈ _
    rw [map_mul, herat, Prod.snd_mul]
    dsimp only
    rw [map_mul, map_inv, map_inv, mul_assoc, hg2, inv_mul_cancel_left]
    refine ⟨_, K.mul_mem (K.inv_mem hkδ) hk, ?_⟩
    simp only [smul_eq_mul]
    group

end GlobalTheory.Mem.VolFin
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient =====
