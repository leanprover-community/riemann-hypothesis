module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.JeigRFinite
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalFixedTensorStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.FixFin
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical TensorProduct




attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem eig_abs (hII : IsoInv) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (w : Pl E)
    (ϖ : (w.adicCompletion E)ˣ) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (τ₁ : Representation ℂ (GLw a w) X) (τ₂ : Representation ℂ (GLw b w) Y) (h₁ : IsAdmissible τ₁) (h₂ : IsAdmissible τ₂) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧
      ∀ (X' Y' : Type) [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
        (ρ₁ : Representation ℂ (GLw a w) X') (ρ₂ : Representation ℂ (GLw b w) Y'), Nonempty (ρ₁.Equiv τ₁) → Nonempty (ρ₂.Equiv τ₂) →
        Module.finrank ℂ (fixed (GlobalTheory.SmGL.extTensor ρ₁ ρ₂) (I2 a b w)) ≤ m ∧
          ∀ ξa ξb, Ev.JEigR w (GlobalTheory.SmGL.extTensor ρ₁ ρ₂) ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  haveI : FiniteDimensional ℂ (fixed (GlobalTheory.SmGL.extTensor τ₁ τ₂) (I2 a b w)) :=
    GlobalTheory.T.finiteDimensional_fixed_tensor _ _ _ _ τ₁ τ₂ _ _
      (h₁.2 _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _) (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _))
      (h₂.2 _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _) (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _))
  refine ⟨_, Module.finrank ℂ (fixed (GlobalTheory.SmGL.extTensor τ₁ τ₂) (I2 a b w)), Ev.jeigR_finite w (GlobalTheory.SmGL.extTensor τ₁ τ₂) ϖ, ?_⟩
  rintro X' Y' _ _ _ _ ρ₁ ρ₂ ⟨Φa⟩ ⟨Φb⟩
  have Φ : (GlobalTheory.SmGL.extTensor ρ₁ ρ₂).Equiv (GlobalTheory.SmGL.extTensor τ₁ τ₂) := GlobalTheory.SmGL.RowOneCell.extTensorEquiv Φa Φb
  exact ⟨(hII _ _ _ _ _ ⟨Φ⟩ (I2 a b w)).2.1.le, fun ξa ξb h => Ev.jeigR_equiv Φ h⟩

theorem admissible_hecke_word_product {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (P : Pre E n) (w : Pl E) :
    IsAdmissible (prodAt P w) :=
  ⟨GlobalTheory.SmGL.isSmooth_parInd _ _, fun K ho hc => fixFin E n P w K ho hc⟩

theorem eig_one (hII : IsoInv) (hSPr : StrictProd) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (PA : Pre E a) (PB : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa : Pre E a) (Pb : Pre E b), Strict Pa PA → Strict Pb PB →
      Module.finrank ℂ (fixed (pairAt Pa Pb w) (I2 a b w)) ≤ m ∧ ∀ ξa ξb, JEig Pa Pb w ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  obtain ⟨Z, m, hZ, h⟩ := eig_abs hII w ϖ (prodAt PA w) (prodAt PB w) (admissible_hecke_word_product PA w) (admissible_hecke_word_product PB w)
  refine ⟨Z, m, hZ, fun Pa Pb ha hb => ?_⟩
  have h' := h _ _ (prodAt Pa w) (prodAt Pb w) (hSPr E a Pa PA ha w) (hSPr E b Pb PB hb w)
  exact ⟨h'.1, fun ξa ξb hj => h'.2 ξa ξb hj⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
