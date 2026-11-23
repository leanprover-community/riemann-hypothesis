module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.SameOfStrict
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
open scoped Classical




attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

def Same {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) (K : Subgroup (GLw n w)) (D D' : Pre E n) : Prop :=
  (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D' w)) ∧
    Module.finrank ℂ ↥(fixed (prodAt D w) K) = Module.finrank ℂ ↥(fixed (prodAt D' w) K) ∧
    FiniteDimensional ℂ ↥(fixed (prodAt D' w) K)

theorem part2 (hSPr : StrictProd) (hSJ : StrictJoin) (hII : IsoInv) (hAd : AdmProd) {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) :
    ∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, Same w (F₀.d₀.K' w) D (Dl j) := by
  intro w hw
  obtain ⟨k, Dl, hD⟩ := joins_fin hSJ F₀.μ F₀.C.a kA kB PA PB
  have hs : ∀ D D' : Pre E n, Strict D D' → Same w (F₀.d₀.K' w) D D' :=
    same_of_strict hSPr hII hAd w _ (F₀.ok₀.K' w hw).1 (F₀.ok₀.K' w hw).2.1
  refine ⟨k, Dl, fun i s₁ s₂ Pa Pb D hc => ?_⟩
  obtain ⟨j, hj⟩ := hD i Pa Pb D hc.ctx.join (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2
  exact ⟨j, hs D (Dl j) hj⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
