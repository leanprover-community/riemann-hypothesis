module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open Classical in
def basisSet (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) : Finset F :=
  (Finset.univ.image fun p : Fin d × Fin d × Fin d => bs.repr (bs p.1 * bs p.2.1) p.2.2) ∪
  (Finset.univ.image fun k : Fin d => bs.repr 1 k) ∪
  (Finset.univ.image fun p : Fin d × Fin d => bs.repr (σ (bs p.1)) p.2) ∪
  {Algebra.discr F (⇑bs), (Algebra.discr F (⇑bs))⁻¹, (2 : F)⁻¹}


open Classical in
def matSet {d : ℕ} (bs : Module.Basis (Fin d) F E) {m : ℕ} (X : Matrix (Fin m) (Fin m) E) : Finset F :=
  (Finset.univ.image fun p : Fin m × Fin m × Fin d => bs.repr (X p.1 p.2.1) p.2.2) ∪
  (Finset.univ.image fun k : Fin d => bs.repr (X.det)⁻¹ k)

def IntAt (v : HeightOneSpectrum (𝓞 F)) (X : Finset F) : Prop :=
  ∀ x ∈ X, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F

def FinInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Finset F), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IntAt v X

def PsiBasic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    (∀ x y, psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y) ∧ psiV F ψ v 0 = 1 ∧ Continuous (psiV F ψ v)

def PsiCond : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ a : Fv F v,
      (∀ b ∈ v.adicCompletionIntegers F, psiV F ψ v (a * b) = 1) ↔ a ∈ v.adicCompletionIntegers F

def LocRing : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)), IntAt v (basisSet σ bs) →
  ∃ (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S),
    (ε = 1 ∨ ε = -1) ∧ (S : Set (Fv F v ⊗[F] E)) = Rv bs v ∧
    (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) ∧
    (∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = x → ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c) ∧
    ϖ ∈ v.adicCompletionIntegers F ∧ ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧
    IsUnrQuad S σS ⟨_, hϖ⟩ (Ideal.absNorm v.asIdeal) ε ∧ ‖(2 : Fv F v)‖ = 1 ∧
    ∀ a : Fv F v ⊗[F] E,
      (∀ b ∈ S, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * b) ∈ v.adicCompletionIntegers F) ↔ a ∈ S

def LocMat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S),
    (S : Set (Fv F v ⊗[F] E)) = Rv bs v → (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) →
  ∀ (m : ℕ) (X : Matrix (Fin m) (Fin m) E), (∀ a b, σ (X b a) = X a b) → X.det ≠ 0 → IntAt v (matSet bs X) →
    ∃ hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S, IsUnimod σS (matS S X hX)

end PositivityTheory.SiegelWeilFormula.Gunr

end
