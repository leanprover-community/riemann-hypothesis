module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs

namespace Re.Asc

theorem hasSpehComp (h3 : Clause3Asc) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N a d : ℕ} (hN : 1 ≤ N)
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {π : CuspSub E a} (hn : IsNormalised π) (e : AscEmb V π d) :
    HasSpehComp V π d := by
  refine ⟨fun w => ?_, h3 E N a d V π hN hV (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn) hn e, fun τ => ?_⟩
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
    obtain ⟨σ', hσ'⟩ := GlobalTheory.DiscLocEx.exists_isLocCompGL hF E N V hV w
    exact ⟨σ, σ', hσ, hσ'⟩
  · obtain ⟨m', hm'⟩ := PInfInd2A.exists_hasInfCharGL hV τ
    obtain ⟨m₀, hm₀, rfl⟩ := infAsc_holds E N a d V π hV e τ m' hm'
    refine ⟨m₀, hm₀, ?_⟩
    have e' : (∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))) = GlobalTheory.SphGal.spehInf d m₀ := by
      simp only [GlobalTheory.SphGal.spehInf, spehExp]
      push_cast
      rfl
    rw [← e']
    exact hm'

section Pair

end Pair

section Local

open GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.BcSpehProof

end Local

end Re.Asc

end PositivityTheory.Rg.Rs

end
