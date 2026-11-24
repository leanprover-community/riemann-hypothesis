module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) (k : Fin m × Fin n × Fin 2) : AF F :=
  (Algebra.TensorProduct.basis (AF F) bs).repr (X k.1 k.2.1) k.2.2

def ev0 (κ : Type) : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ where
  toFun Φ := Φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Ek {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (k : Fin m × Fin n × Fin 2) : Mx F E m n :=
  Matrix.single k.1 k.2.1 ((1 : AF F) ⊗ₜ[F] bs k.2.2)

def Bf {m n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (X Z : Mx F E m n) : AF F :=
  Algebra.trace (AF F) (AE F E) (Xᵀ * incM F J * Z.map (cA σ)).trace

def IsAdapted {m n : ℕ} {σ : E →ₐ[F] E} (bs : Module.Basis (Fin 2) F E) (A : Spc F E m) (Y : Spc F E n)
    (b : GL (Fin n ⊕ Fin n) E)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2)) : Prop :=
  ∀ Z X : Mx F E m n, dd.e (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) = (crdB bs X, fun k => Bf σ A.J Z (Ek bs k))

def SDarb : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (bs : Module.Basis (Fin 2) F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (r s : ℕ), B.IsGood σ → 1 ≤ m → 1 ≤ n →
  (A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j) →
  IsFrame2 σ Y b → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2),
    IsAdapted bs A Y b dd ∧ ∀ x : Matrix (Fin m) (Fin n ⊕ Fin n) E, ∃ y z : Fin m × Fin n × Fin 2 → F,
      dd.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

def SEv : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (bs : Module.Basis (Fin 2) F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (r s : ℕ), B.IsGood σ → 1 ≤ m → 1 ≤ n →
  (A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j) →
  IsFrame2 σ Y b → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∀ dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2),
    IsAdapted bs A Y b dd →
    ev0 (F := F) (Fin m × Fin n × Fin 2) ∈ (adeleClass F).adm (Fin m × Fin n × Fin 2) ∧
    (∀ z : Matrix (Fin m) (Fin n) (AE F E), ∀ Φ ∈ schA F (Fin m × Fin n × Fin 2),
      ev0 _ (dd.rho B.ψ (z * (diagCols (Fin n))ᵀ) Φ) = ev0 _ Φ) ∧
    ∀ Φ ∈ schA F (Fin m × Fin n × Fin 2), HasSum (fun y : Matrix (Fin m) (Fin n) E =>
      ev0 _ (dd.rho B.ψ (incM F (Matrix.fromCols y (-y))) Φ)) (thetaSum F Φ)

end PositivityTheory.SiegelWeilFormula.Ald

end
