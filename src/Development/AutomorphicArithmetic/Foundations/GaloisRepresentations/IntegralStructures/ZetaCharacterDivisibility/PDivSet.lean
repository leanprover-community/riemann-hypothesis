module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divSet_of :
    DivWCoreLac → SenWLac → LacBridge → InFacts → DivSet := by
  intro hcore hsen hlac _ E Ω _ _ _ _ _ l _ a dd ρ hρ hss hHT ψ hψ hD
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : IsGalois E Ω := {}
  have : CompactSpace (G E Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[E] Ω))
  obtain ⟨K', _, _, _, X, hX, hroots⟩ := hsen E Ω l dd a ρ hρ (hlac E Ω l a dd ρ hHT)
  let T : G E Ω → (Qbar l)[X] → Prop := fun g Q => Q.Monic ∧ Q.natDegree = a ∧
    aeval (ρ g : Matrix (Fin dd) (Fin dd) (Qbar l)) Q = 0 ∧
      ((ψ g : (Qbar l)ˣ) : Qbar l) = (-1) ^ a * Q.coeff 0
  let P : G E Ω → (Qbar l)[X] := fun g => if h : ∃ Q, T g Q then h.choose else 1
  have hP : ∀ s ∈ {g : G E Ω | ∃ Q, T g Q}, T s (P s) := by
    intro s hs
    have e : P s = (show ∃ Q, T s Q from hs).choose := dif_pos hs
    rw [e]
    exact (show ∃ Q, T s Q from hs).choose_spec
  have hss' : IsSSMat ρ := by
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W hW
    exact ⟨W', h2, h1⟩
  obtain ⟨r, hrc, hrss, hin, hco, -, -, -, hopen, hdense, -, -⟩ :=
    hcore (G E Ω) (Qbar l) K' dd a ρ (Units.continuous_val.comp hρ) hss'
      {g : G E Ω | ∃ Q, T g Q} hD P
      (fun s hs => ⟨(hP s hs).1, (hP s hs).2.1⟩) (fun s hs => (hP s hs).2.2.1)
      X hX hroots ψ (Units.continuous_val.comp hψ) (fun s hs => (hP s hs).2.2.2)
  refine ⟨r, ?_, ?_, hin, hco, hopen, hdense⟩
  · refine Units.continuous_iff.mpr ⟨hrc, ?_⟩
    simp only [← map_inv]
    exact hrc.comp continuous_inv
  · intro W hW
    obtain ⟨W', h1, h2⟩ := hrss W hW
    exact ⟨W', h2, h1⟩
