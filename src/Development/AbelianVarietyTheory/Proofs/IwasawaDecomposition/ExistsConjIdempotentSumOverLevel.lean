module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.HalfLevelConj

theorem exists_conj_idemSum : ∀ (D : D7) (N : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P →
    (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)),
    IsIdemSum e' P' ∧ (∀ PP ∈ P', ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ cA D e' = e := by
  intro D N e P hE hN
  classical
  refine ⟨cA D e, P.image Formalism.L2.DIV.conjPl, Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hE, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    have hmem : ((N : ℕ) : 𝓞 D.host.E) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔
        Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := Iff.rfl
    have hs : Formalism.L2.DIV.starO ((N : ℕ) : 𝓞 D.host.E) = ((N : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      rw [Formalism.L2.DIV.starO_coe]
      simp
    rw [hmem, hs]
    exact hN PP hPP
  · rw [Formalism.L2.Theta.cA_cA]

end GlobalTheory.HalfLevelConj
