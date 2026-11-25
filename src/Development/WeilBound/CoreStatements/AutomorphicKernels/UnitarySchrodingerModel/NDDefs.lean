module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
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

section LocS

namespace PositivityTheory.PfSWUS.Loc

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def trPair (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (∑ a, ∑ c, S a c * T c a)

def jtR (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : R → ℂ) (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (b : HermR R σ n) : ℂ :=
  ∫ Y, φ Y * ψR (trPair R (b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (gramR R σ J Y)) ∂μ

def latO {d n : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fin n → Fv F v ⊗[F] E) :=
  {y | ∀ a k, (Algebra.TensorProduct.basis (Fv F v) bs).repr (y a) k ∈ v.adicCompletionIntegers F}

def IsSchwartzInf {n M : ℕ} (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) : Prop :=
  ∀ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
    ∃ f : SchwartzMap (Fin N → ℝ) ℂ, ∀ x, f x = Φinf (e.symm x)

end PositivityTheory.PfSWUS.Loc

end LocS

section D7S

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

def WhitNDg : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ g : G D n,
    HolValueAt (fun z => ∫ b, npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ (ω g Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam)
      (s0 V n) (IfrB V ν (ω g Φ).1 β)

def NDOfWhit : Prop := Unfold → ThetaCoef → WhitNDg → CoefND

end PositivityTheory.PfSWUS

namespace PositivityTheory.PfSWUS

end PositivityTheory.PfSWUS

end D7S

end
