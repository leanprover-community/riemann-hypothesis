module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
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

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

def RelAlg : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : SD σ), ∃ (η : E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n),
    η ≠ 0 ∧ (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) ∧
    (∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)) ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = 0 → y = 0) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd d η) ∧
    ∀ T : nF σ d.Y d.b, IsND T → ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ ∧
      (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0

def SdEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J →
  ∀ ψ : AddChar (AF F) ℂ, HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F ψ → ∀ n : ℕ,
    (∃ μ, HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ M J (AF F) ψ n μ) ∧ ∃ ν, HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) ψ n ν

end PositivityTheory.SiegelWeilFormula.KWhit

end
