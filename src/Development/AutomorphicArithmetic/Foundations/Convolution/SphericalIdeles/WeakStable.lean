module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ
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

open NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory.C GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

def SatDict : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (π : CuspSub K n) (v : Pl K)
    (τ : SmIrr (Gw n v)), (Cusp.cx π).locComp v τ →
      ((∃ B, (Cusp.cx π).sat v B) → IsSpherical τ.ρ) ∧
      (IsSpherical τ.ρ → ∃ α : Fin n → ℂˣ, IsSubquotient τ.ρ (prinSeries fun i => unrChar (v.adicCompletion K) (α i))) ∧
      ∀ α : Fin n → ℂˣ, IsSpherical τ.ρ → IsSubquotient τ.ρ (prinSeries fun i => unrChar (v.adicCompletion K) (α i)) →
        (Cusp.cx π).sat v (Finset.univ.val.map fun i => α i ^ ε)

def UnlSph : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v : Pl K) (τ : SmIrr (Gw n v)) (α : Fin n → ℂˣ),
    (∀ i j, (α i : ℂ) ≠ (Ideal.absNorm v.asIdeal : ℂ) * α j) →
    IsSubquotient τ.ρ (prinSeries fun i => unrChar (v.adicCompletion K) (α i)) → IsSpherical τ.ρ

def UnrNorm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (w : PlacesOver E v)
    (σw : w.1.adicCompletion E ≃+* w.1.adicCompletion E) (l : ℕ) (N : (w.1.adicCompletion E)ˣ →* (v.adicCompletion F)ˣ),
    UpperTheory.Gal.Join.IsNorm (completionMap v w.1) σw l N → Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal → ∀ a : ℂˣ,
      (unrChar (v.adicCompletion F) a).comp N = unrChar (w.1.adicCompletion E) a

def WeakStable : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [_root_.NumberField.IsTotallyComplex K]
    [_root_.NumberField.IsTotallyComplex M], (Module.finrank K M).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub M n),
    UpperTheory.V.Published.WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → (∀ g : M ≃ₐ[K] M, (Cusp.cx P).ConjIso g.toRingEquiv) ∧
      (∀ v, ∃ τ, (Cusp.cx π).locComp v τ) ∧ ∀ w, ∃ τ', (Cusp.cx P).locComp w τ'

end UpperTheory.ConvolutionTheory.Sph
