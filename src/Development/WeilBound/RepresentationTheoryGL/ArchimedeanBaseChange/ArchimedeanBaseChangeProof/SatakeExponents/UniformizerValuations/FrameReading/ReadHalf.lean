module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PChiPin
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical



namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Pin

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem chi_pin (gen : Γ → Prod' H d) (a₀ : Γ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (ha₀ : (gen a₀).2 v = v)
    (s : ι) (X : H s →L[ℂ] H s)
    (χ : StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X})
      →⋆ₐ[ℂ] ℂ)
    (heig : ∀ a : StarAlgebra.adjoin ℂ (Set.range gen), a.1.2 v ≠ 0 → ∃ c : ℂ, a.1.2 v = c • v ∧
      χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c)
    (a : StarAlgebra.adjoin ℂ (Set.range gen)) (c : ℂ) (hc : a.1.2 v = c • v) :
    χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c :=
  ChiPin.chi_pin gen a₀ v hv ha₀ s X χ heig a c hc

end Pin



def BlockCand : Prop := ∀ (hR : Rd.ReadLimit) (hD : DiagAlg) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∀ n : ℕ, 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (S T : Finset (Pl E)) (F₀ : Frame0 hR π S)
    (F : RunFrame F₀ T) (h : F.Struct),
    GRead (H := (F.toGenIn hD h).H) (F.toGenIn hD h).gen (F.toGenIn hD h).βop (F.toGenIn hD h).m (F.toGenIn hD h).v
      (∃ (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i)) (Pb : Pre E (n - F₀.C.a i))
        (D : Pre E n) (A : Type) (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ),
        F₀.Cand F.d i s₁ s₂ Pa Pb D ∧ (∀ j, G j ∈ pairSpace s₁.space s₂.space) ∧
        (∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j)) ∧
        (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0 ∧
        (∀ τ lam, HasWeightAt π τ lam → ∑ k, D.m k τ = infOfWeight lam) ∧
        (∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w))

theorem gRead_mono {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
    [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type} (gen : Γ → Prod' H d) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ)
    (v : EuclideanSpace ℂ (Fin d)) {P Q : Prop} (hPQ : P → Q) (h : GRead gen β m v P) : GRead gen β m v Q :=
  fun s χ h1 h2 h3 => hPQ (h s χ h1 h2 h3)


theorem frameRead_of (h1 : BlockCand) (h2 : CandTOut) : FrameRead := by
  intro hR hD E _ _ _ hE n hn π hπ S T F₀ F h
  refine gRead_mono _ _ _ _ ?_ (h1 hR hD E hE n hn π hπ S T F₀ F h)
  rintro ⟨i, s₁, s₂, Pa, Pb, D, A, G, hc, hG, hl, hne, hwt, hgood⟩
  exact ⟨D, h2 hR E hE n hn π hπ S T F₀ F h i s₁ s₂ Pa Pb D A G hc hG hl hne hwt hgood⟩

end PositivityTheory.Rg.BcB.F

end
