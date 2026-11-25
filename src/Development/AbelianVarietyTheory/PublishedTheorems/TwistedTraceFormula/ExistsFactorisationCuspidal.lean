module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleModule.Rank
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
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.AutMult
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
open Formalism.MainNotions.SchurIrreducible (Pl)
open GlobalTheory.PRep (IsAdmissible fixed)
open scoped InnerProductSpace

namespace GlobalTheory

namespace Flath

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

abbrev finFactor (R : ∀ v, IrrU (GPl σ J v)) (v : HeightOneSpectrum (𝓞 F)) :
    GLoc σ J v →* ((R (.inr v)).H →L[ℂ] (R (.inr v)).H) := (R (.inr v)).π

def IsUnramFactorisation {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (R : ∀ v, IrrU (GPl σ J v))
    (ξ : ∀ v, (R v).H) (π : GAd σ J →* (H →L[ℂ] H)) (B : (∀ v, (R v).H) → H) : Prop :=
  IsFactorisation σ J (fun v => (R v).π) ξ π B ∧
  (∀ v, (smRep (finFactor R v)).IsIrreducible ∧ IsAdmissible (smRep (finFactor R v))) ∧
  ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L →
    ∀ᶠ v in cofinite, fixed (toRep (finFactor R v)) (stabLoc σ J L v) = ℂ ∙ ξ (.inr v)

end Flath

namespace Published

def FlathFactorisation : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π →
        ∃ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), Flath.IsUnramFactorisation R ξ π B

end Published

end GlobalTheory

end
