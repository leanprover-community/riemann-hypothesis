module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular

@[expose] public section

noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.KapLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def stdH (w : Pl E) {n : ℕ} (v v' : Fin n → w.adicCompletion E) : w.adicCompletion E :=
  ∑ k, v k * cj w (v' k)

def Bridge (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) : Prop :=
  (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧
    (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2

def Fits (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (Q : (w.adicCompletion E)[X]) (u : B.A) : Prop :=
  Algebra.adjoin K.E {u} = ⊤ ∧ aeval u (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧
    u * B.σ u = 1

def IsModel (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : Prop :=
  ∃ ψ : B.A ≃+ (Fin n → w.adicCompletion E), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧
    (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧ ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

def congSet (w : Pl E) (n k : ℕ) : Set (GLw n w) :=
  {g | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
    WithZero.exp (-(k : ℤ))}

theorem cast_finsum {α : Type*} (f : α → ℚ) : ((∑ᶠ a, f a : ℚ) : ℂ) = ∑ᶠ a, (f a : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h' : ¬ (Function.support fun a => (f a : ℂ)).Finite := by
      simpa [Function.support] using h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h']
    simp

end GlobalTheory.KapLat
