module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
open Formalism.UG (GLint)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsElemDiv {v : HeightOneSpectrum (𝓞 F)} (x : GL (Fin n) (Fv F v)) (d : Fin n → (Fv F v)ˣ) : Prop :=
  ∃ k₁ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
    ∃ k₂ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
      x.1 = k₁.1 * Matrix.diagonal (fun i => (d i : Fv F v)) * k₂.1

def IsInertUnder (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  (v : HeightOneSpectrum (𝓞 F))

def latMoved (g : GLoc σ J v) : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) :=
  (latLoc F L v).comap ((Matrix.mulVecLin (matHom (Fv F v) σ J g⁻¹).1).restrictScalars (intLoc F E v))

def latLength (g : GLoc σ J v) : ℕ∞ :=
  Module.length (intLoc F E v)
    (latLoc F L v ⧸ (latLoc F L v ⊓ latMoved σ J L v g).submoduleOf (latLoc F L v))

def graphHgt (g : GLoc σ J v) : ℝ≥0 :=
  hgtFin σ (dblGram finSumFinEquiv J) L v (ioH (Fv F v) σ rfl (g, 1))

def SplitAt (h : IsCMExt F E σ) (hJ : IsHermND σ J) : Prop :=
  ∀ (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)), IsSplitBasis τ L β → ∀ g : GLoc σ J v,
    (∃ d, IsElemDiv (splitEquivIn h hJ τ β g) d) ∧
    (∀ d, IsElemDiv (splitEquivIn h hJ τ β g) d →
      graphHgt σ J L v g = ∏ i, min ‖(d i : Fv F v)‖₊ ‖(d i : Fv F v)‖₊⁻¹) ∧
    graphHgt σ J L v g ≤ 1

def InertAt : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v,
    (∃ l : ℕ, latLength σ J L v g = l ∧
      graphHgt σ J L v g = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ))) ∧
    graphHgt σ J L v g ≤ 1

def GraphNormFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    IsSelfDualAt σ J L v → SplitAt σ J L v h hJ ∧ InertAt σ J L v

omit [NumberField E] in
theorem mem_latMoved {g : GLoc σ J v} {x : Fin n → Fv F v ⊗[F] E} :
    x ∈ latMoved σ J L v g ↔ (matHom (Fv F v) σ J g⁻¹).1 *ᵥ x ∈ latLoc F L v := Iff.rfl


end GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice

end
