module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def cv (R : Type) [CommRing R] [Algebra F R] {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (x : Fin M → R ⊗[F] E) : Fin M × Fin d → R :=
  fun p => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2

def gmat (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (h : HA R σ J) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
  fun p q => (Algebra.TensorProduct.basis R b).repr
    ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2

def ofF {d M : ℕ} (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) : Fin 1 → Fin M → E :=
  fun _ i => ∑ k, x (i, k) • b k

end Coord

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def gfin (σ : E →ₐ[F] E) {d M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (h : HA (AF F) σ J) : Matrix (Fin M × Fin d) (Fin M × Fin d) (Af F) :=
  (gmat (AF F) σ J b h⁻¹).map (sndA F)

def ginf (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (σ : E →ₐ[F] E) {d M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (h : HA (AF F) σ J)
    (w : InfinitePlace F) : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ :=
  (gmat (AF F) σ J b h⁻¹).map fun t => e (fstA F t) w

def xw (e : Ainf F ≃+* (InfinitePlace F → ℝ)) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) : Fin M × Fin d → ℝ :=
  fun p => e (cv (Ainf F) b (X 0) p) w

def gaussQ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) : ℝ :=
  Real.exp (-Real.pi * ∑ w, xw e b X w ⬝ᵥ (Pm w *ᵥ xw e b X w))

def prH {G : Type} [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) : Measure G :=
  (μ 𝓕)⁻¹ • μ.restrict 𝓕

end Adelic

end GlobalTheory.CompanionTheory.SW.BB
