module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.InfMatchOf
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical



attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF PositivityTheory.Rg.BcB.F.borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities.GelfandReading

private theorem valA_single {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ}
    (f : List (Bool × ℕ) → Inf m → ℂ)
    (hf : ∀ (s : Bool) (k : ℕ) (χ : Inf m), f [(s, k)] χ = GlobalTheory.Dec.gelfVal (χ s) k * f [] χ)
    (v : InfinitePlace E) (s : Bool) (k : ℕ) (χ : InfinitePlace E → Inf m) :
    valA (fun v' => f (if v' = v then [(s, k)] else [])) χ =
      GlobalTheory.Dec.gelfVal (χ v s) k * valA (fun _ : InfinitePlace E => f []) χ := by
  unfold valA
  have h : ∀ v' : InfinitePlace E, f (if v' = v then [(s, k)] else []) (χ v') =
      (if v' = v then GlobalTheory.Dec.gelfVal (χ v s) k else 1) * f [] (χ v') := by
    intro v'
    by_cases hv : v' = v
    · subst hv
      simp [hf]
    · simp [hv]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

end UpperTheory.BaseChangeIdentities.GelfandReading

theorem UpperTheory.BaseChangeIdentities.GelfandReading.pDerVal :
    UpperTheory.BaseChangeIdentities.GelfandReading.DerVal := by
  intro E _ _ _ a b l₁ l₂ μ₁ μ₂ μa μb A κ _ ψ ψ' r r' v s k χa χb
  have hw : ∀ {m : ℕ} (s : Bool) (k : ℕ) (χ : Inf m),
      A.valW [(s, k)] χ = GlobalTheory.Dec.gelfVal (χ s) k * A.valW [] χ := by
    intro m s k χ
    simp [Arch.valW, zVal]
  constructor
  · have h := UpperTheory.BaseChangeIdentities.GelfandReading.valA_single (fun w => A.valW (m := a) w) hw v s k χa
    simp only [PT.val, Arch.pt]
    rw [h]
    ring
  · have h := UpperTheory.BaseChangeIdentities.GelfandReading.valA_single (fun w => A.valW (m := b) w) hw v s k χb
    simp only [PT.val, Arch.pt]
    rw [h]
    ring

end
