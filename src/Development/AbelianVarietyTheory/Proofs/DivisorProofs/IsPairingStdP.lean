module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

section Real

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

def schrF (P : V → V → ℝ) (w : V × V) (f : V → ℂ) : V → ℂ :=
  fun y => Complex.exp (-(2 * Real.pi * Complex.I) * ((P y w.2 + P w.1 w.2 / 2 : ℝ) : ℂ)) * f (y + w.1)

def omega (P : V → V → ℝ) (w w' : V × V) : ℝ := P w.1 w'.2 - P w'.1 w.2

structure IsPairing (P : V → V → ℝ) : Prop where
  addL : ∀ x x' y, P (x + x') y = P x y + P x' y
  addR : ∀ x y y', P x (y + y') = P x y + P x y'
  smulL : ∀ (c : ℝ) x y, P (c • x) y = c * P x y
  smulR : ∀ (c : ℝ) x y, P x (c • y) = c * P x y
  nondegL : ∀ x, (∀ y, P x y = 0) → x = 0
  nondegR : ∀ y, (∀ x, P x y = 0) → y = 0

end Real

section Adelic

open scoped Matrix
open NumberField GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

variable (F) in
def trP (κ : Type) [Fintype κ] (y b : κ → mixedEmbedding.mixedSpace F) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i)

def locV {κ : Type} (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

end Adelic

end GlobalTheory.ArchUniq
