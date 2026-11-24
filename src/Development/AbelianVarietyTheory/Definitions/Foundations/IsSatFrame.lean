module

public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import Mathlib.Data.EReal.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory.FGDepth

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C]

def toE (x : WithTop ℝ) : EReal := (WithBot.some x : WithBot (WithTop ℝ))

def mfact {σ : Type} (α : σ →₀ ℕ) : C := α.prod fun _ n => (n.factorial : C)

def derivAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ α ∈ P.support, P.coeff α * mfact α * coeff α g

def content (v : AddValuation C (WithTop ℝ)) {σ : Type} (P : MvPolynomial σ C) : EReal :=
  ⨅ α ∈ P.support, toE (v (P.coeff α * mfact α))

variable {v : AddValuation C (WithTop ℝ)}

def IsExp {d : ℕ} (G : LogFGL v d) (ex : Fin d → MvPowerSeries (Fin d) C) : Prop :=
  (∀ a, constantCoeff (ex a) = 0) ∧ ∀ a, subst ex (G.lg a) = X a

def expOf {d : ℕ} (G : LogFGL v d) : Fin d → MvPowerSeries (Fin d) C :=
  Classical.epsilon (IsExp G)

def expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) :
    (Σ b, Fin (d b)) → MvPowerSeries (Σ b, ι b) C :=
  fun x => subst (fun e : Fin (d x.1) =>
    ∑ a, u x.1 a e • (X ⟨x.1, a⟩ : MvPowerSeries (Σ b, ι b) C)) (expOf (G x.1) x.2)

def depth {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C) : EReal :=
  ⨅ f : {f : MvPowerSeries (Σ b, Fin (d b)) C // MvIsInt v f},
    toE (v (derivAt0 P (subst (expAlong G u) f.1)))

def detPow (C : Type) [Field C] (i c : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) C :=
  (Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C))) ^ c

def IsSatFrame (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (u : Fin i → Fin d → C) : Prop :=
  (∀ a e, IsIntV v (u a e)) ∧
    ∃ r : Fin i → Fin d, v (Matrix.det (Matrix.of fun a b => u a (r b))) = 0

def detDepth {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C) (c : ℕ) : EReal :=
  depth (fun _ : Fin i => G) (fun _ => u) (detPow C i c)

def IsCharLog {d : ℕ} (G : LogFGL v d) (l : Fin d → C) : Prop :=
  ∃ χ : MvPowerSeries (Fin d) C, MvIsInt v χ ∧
    ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => l e ^ n / (n.factorial : C)

end

end GlobalTheory.FGDepth
