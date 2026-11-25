module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGen
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd

variable {D : D7} {n : ℕ}

def IsMonoFock (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : Mx D V.rank n → ℂ) : Prop :=
  ∃ (e : D.what₂.Tau × Fin V.rank × Fin n × Bool →₀ ℕ) (c : ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) (d : ℕ)
    (bs : Module.Basis (Fin d) D.host.F D.host.E)
    (gv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      (Fin n → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ),
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv ∧
    φ = fun x => evalPoly (MvPolynomial.monomial e c) (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))

def FockSplitK : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ k ∈ K D n, ∃ (N : ℕ) (φs : Fin N → Mx D V.rank n → ℂ),
    (ω k Φ).1 = ∑ j, φs j ∧ ∀ j, IsMonoFock θ V l s (φs j)

def WhitTAdd : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ a : GL (Fin n) (AE D), ∀ g : G D n,
  ∀ (N : ℕ) (φs : Fin N → Mx D V.rank n → ℂ), (∀ j, IsMonoFock θ V l s (φs j)) →
    ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      whitT ψ V μ lam nb w H (∑ j, φs j) (adj a.1 * β.1.map (incA D) * a.1) g z =
        ∑ j, whitT ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) g z

def IfrBAdd : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ a : GL (Fin n) (AE D),
  ∀ (N : ℕ) (φs : Fin N → Mx D V.rank n → ℂ), (∀ j, IsMonoFock θ V l s (φs j)) →
    IfrB V ν (fun x => (∑ j, φs j) (HMul.hMul x a.1)) β = ∑ j, IfrB V ν (fun x => φs j (HMul.hMul x a.1)) β

def MatchMono : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ a : GL (Fin n) (AE D), ∀ k ∈ K D n,
  ∀ φ : Mx D V.rank n → ℂ, IsMonoFock θ V l s φ →
    MatchGenA ψ V μ lam nb w H φ (adj a.1 * β.1.map (incA D) * a.1) k β
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) * IfrB V ν (fun x => φ (HMul.hMul x a.1)) β)

def DictKAOfParts : Prop := FockSplitK → WhitTAdd → IfrBAdd → MatchMono → DictKA

end PositivityTheory.PfSWUS

end
